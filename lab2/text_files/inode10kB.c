// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (C) 2007 Oracle.  All rights reserved.
 */

#include <crypto/hash.h>
#include <linux/kernel.h>
#include <linux/bio.h>
#include <linux/blk-cgroup.h>
#include <linux/file.h>
#include <linux/fs.h>
#include <linux/pagemap.h>
#include <linux/highmem.h>
#include <linux/time.h>
#include <linux/init.h>
#include <linux/string.h>
#include <linux/backing-dev.h>
#include <linux/writeback.h>
#include <linux/compat.h>
#include <linux/xattr.h>
#include <linux/posix_acl.h>
#include <linux/falloc.h>
#include <linux/slab.h>
#include <linux/ratelimit.h>
#include <linux/btrfs.h>
#include <linux/blkdev.h>
#include <linux/posix_acl_xattr.h>
#include <linux/uio.h>
#include <linux/magic.h>
#include <linux/iversion.h>
#include <linux/swap.h>
#include <linux/migrate.h>
#include <linux/sched/mm.h>
#include <linux/iomap.h>
#include <asm/unaligned.h>
#include <linux/fsverity.h>
#include "misc.h"
#include "ctree.h"
#include "disk-io.h"
#include "transaction.h"
#include "btrfs_inode.h"
#include "print-tree.h"
#include "ordered-data.h"
#include "xattr.h"
#include "tree-log.h"
#include "bio.h"
#include "compression.h"
#include "locking.h"
#include "free-space-cache.h"
#include "props.h"
#include "qgroup.h"
#include "delalloc-space.h"
#include "block-group.h"
#include "space-info.h"
#include "zoned.h"
#include "subpage.h"
#include "inode-item.h"
#include "fs.h"
#include "accessors.h"
#include "extent-tree.h"
#include "root-tree.h"
#include "defrag.h"
#include "dir-item.h"
#include "file-item.h"
#include "uuid-tree.h"
#include "ioctl.h"
#include "file.h"
#include "acl.h"
#include "relocation.h"
#include "verity.h"
#include "super.h"
#include "orphan.h"

struct btrfs_iget_args {
	u64 ino;
	struct btrfs_root *root;
};

struct btrfs_dio_data {
	ssize_t submitted;
	struct extent_changeset *data_reserved;
	bool data_space_reserved;
	bool nocow_done;
};

struct btrfs_dio_private {
	/* Range of I/O */
	u64 file_offset;
	u32 bytes;

	/* This must be last */
	struct btrfs_bio bbio;
};

static struct bio_set btrfs_dio_bioset;

struct btrfs_rename_ctx {
	/* Output field. Stores the index number of the old directory entry. */
	u64 index;
};

static const struct inode_operations btrfs_dir_inode_operations;
static const struct inode_operations btrfs_symlink_inode_operations;
static const struct inode_operations btrfs_special_inode_operations;
static const struct inode_operations btrfs_file_inode_operations;
static const struct address_space_operations btrfs_aops;
static const struct file_operations btrfs_dir_file_operations;

static struct kmem_cache *btrfs_inode_cachep;

static int btrfs_setsize(struct inode *inode, struct iattr *attr);
static int btrfs_truncate(struct btrfs_inode *inode, bool skip_writeback);
static noinline int cow_file_range(struct btrfs_inode *inode,
				   struct page *locked_page,
				   u64 start, u64 end, int *page_started,
				   unsigned long *nr_written, int unlock,
				   u64 *done_offset);
static struct extent_map *create_io_em(struct btrfs_inode *inode, u64 start,
				       u64 len, u64 orig_start, u64 block_start,
				       u64 block_len, u64 orig_block_len,
				       u64 ram_bytes, int compress_type,
				       int type);

static void __cold btrfs_print_data_csum_error(struct btrfs_inode *inode,
		u64 logical_start, u8 *csum, u8 *csum_expected, int mirror_num)
{
	struct btrfs_root *root = inode->root;
	const u32 csum_size = root->fs_info->csum_size;

	/* Output without objectid, which is more meaningful */
	if (root->root_key.objectid >= BTRFS_LAST_FREE_OBJECTID) {
		btrfs_warn_rl(root->fs_info,
"csum failed root %lld ino %lld off %llu csum " CSUM_FMT " expected csum " CSUM_FMT " mirror %d",
			root->root_key.objectid, btrfs_ino(inode),
			logical_start,
			CSUM_FMT_VALUE(csum_size, csum),
			CSUM_FMT_VALUE(csum_size, csum_expected),
			mirror_num);
	} else {
		btrfs_warn_rl(root->fs_info,
"csum failed root %llu ino %llu off %llu csum " CSUM_FMT " expected csum " CSUM_FMT " mirror %d",
			root->root_key.objectid, btrfs_ino(inode),
			logical_start,
			CSUM_FMT_VALUE(csum_size, csum),
			CSUM_FMT_VALUE(csum_size, csum_expected),
			mirror_num);
	}
}

/*
 * btrfs_inode_lock - lock inode i_rwsem based on arguments passed
 *
 * ilock_flags can have the following bit set:
 *
 * BTRFS_ILOCK_SHARED - acquire a shared lock on the inode
 * BTRFS_ILOCK_TRY - try to acquire the lock, if fails on first attempt
 *		     return -EAGAIN
 * BTRFS_ILOCK_MMAP - acquire a write lock on the i_mmap_lock
 */
int btrfs_inode_lock(struct btrfs_inode *inode, unsigned int ilock_flags)
{
	if (ilock_flags & BTRFS_ILOCK_SHARED) {
		if (ilock_flags & BTRFS_ILOCK_TRY) {
			if (!inode_trylock_shared(&inode->vfs_inode))
				return -EAGAIN;
			else
				return 0;
		}
		inode_lock_shared(&inode->vfs_inode);
	} else {
		if (ilock_flags & BTRFS_ILOCK_TRY) {
			if (!inode_trylock(&inode->vfs_inode))
				return -EAGAIN;
			else
				return 0;
		}
		inode_lock(&inode->vfs_inode);
	}
	if (ilock_flags & BTRFS_ILOCK_MMAP)
		down_write(&inode->i_mmap_lock);
	return 0;
}

/*
 * btrfs_inode_unlock - unock inode i_rwsem
 *
 * ilock_flags should contain the same bits set as passed to btrfs_inode_lock()
 * to decide whether the lock acquired is shared or exclusive.
 */
void btrfs_inode_unlock(struct btrfs_inode *inode, unsigned int ilock_flags)
{
	if (ilock_flags & BTRFS_ILOCK_MMAP)
		up_write(&inode->i_mmap_lock);
	if (ilock_flags & BTRFS_ILOCK_SHARED)
		inode_unlock_shared(&inode->vfs_inode);
	else
		inode_unlock(&inode->vfs_inode);
}

/*
 * Cleanup all submitted ordered extents in specified range to handle errors
 * from the btrfs_run_delalloc_range() callback.
 *
 * NOTE: caller must ensure that when an error happens, it can not call
 * extent_clear_unlock_delalloc() to clear both the bits EXTENT_DO_ACCOUNTING
 * and EXTENT_DELALLOC simultaneously, because that causes the reserved metadata
 * to be released, which we want to happen only when finishing the ordered
 * extent (btrfs_finish_ordered_io()).
 */
static inline void btrfs_cleanup_ordered_extents(struct btrfs_inode *inode,
						 struct page *locked_page,
						 u64 offset, u64 bytes)
{
	unsigned long index = offset >> PAGE_SHIFT;
	unsigned long end_index = (offset + bytes - 1) >> PAGE_SHIFT;
	u64 page_start = 0, page_end = 0;
	struct page *page;

	if (locked_page) {
		page_start = page_offset(locked_page);
		page_end = page_start + PAGE_SIZE - 1;
	}

	while (index <= end_index) {
		/*
		 * For locked page, we will call end_extent_writepage() on it
		 * in run_delalloc_range() for the error handling.  That
		 * end_extent_writepage() function will call
		 * btrfs_mark_ordered_io_finished() to clear page Ordered and
		 * run the ordered extent accounting.
		 *
		 * Here we can't just clear the Ordered bit, or
		 * btrfs_mark_ordered_io_finished() would skip the accounting
		 * for the page range, and the ordered extent will never finish.
		 */
		if (locked_page && index == (page_start >> PAGE_SHIFT)) {
			index++;
			continue;
		}
		page = find_get_page(inode->vfs_inode.i_mapping, index);
		index++;
		if (!page)
			continue;

		/*
		 * Here we just clear all Ordered bits for every page in the
		 * range, then btrfs_mark_ordered_io_finished() will handle
		 * the ordered extent accounting for the range.
		 */
		btrfs_page_clamp_clear_ordered(inode->root->fs_info, page,
					       offset, bytes);
		put_page(page);
	}

	if (locked_page) {
		/* The locked page covers the full range, nothing needs to be done */
		if (bytes + offset <= page_start + PAGE_SIZE)
			return;
		/*
		 * In case this page belongs to the delalloc range being
		 * instantiated then skip it, since the first page of a range is
		 * going to be properly cleaned up by the caller of
		 * run_delalloc_range
		 */
		if (page_start >= offset && page_end <= (offset + bytes - 1)) {
			bytes = offset + bytes - page_offset(locked_page) - PAGE_SIZE;
			offset = page_offset(locked_page) + PAGE_SIZE;
		}
	}

	return btrfs_mark_ordered_io_finished(inode, NULL, offset, bytes, false);
}

static int btrfs_dirty_inode(struct btrfs_inode *inode);

static int btrfs_init_inode_security(struct btrfs_trans_handle *trans,
				     struct btrfs_new_inode_args *args)
{
	int err;

	if (args->default_acl) {
		err = __btrfs_set_acl(trans, args->inode, args->default_acl,
				      ACL_TYPE_DEFAULT);
		if (err)
			return err;
	}
	if (args->acl) {
		err = __btrfs_set_acl(trans, args->inode, args->acl, ACL_TYPE_ACCESS);
		if (err)
			return err;
	}
	if (!args->default_acl && !args->acl)
		cache_no_acl(args->inode);
	return btrfs_xattr_security_init(trans, args->inode, args->dir,
					 &args->dentry->d_name);
}

/*
 * this does all the hard work for inserting an inline extent into
 * the btree.  The caller should have done a btrfs_drop_extents so that
 * no overlapping inline items exist in the btree
 */
static int insert_inline_extent(struct btrfs_trans_handle *trans,
				struct btrfs_path *path,
				struct btrfs_inode *inode, bool extent_inserted,
				size_t size, size_t compressed_size,
				int compress_type,
				struct page **compressed_pages,
				bool update_i_size)
{
	struct btrfs_root *root = inode->root;
	struct extent_buffer *leaf;
	struct page *page = NULL;
	char *kaddr;
	unsigned long ptr;
	struct btrfs_file_extent_item *ei;
	int ret;
	size_t cur_size = size;
	u64 i_size;

	ASSERT((compressed_size > 0 && compressed_pages) ||
	       (compressed_size == 0 && !compressed_pages));

	if (compressed_size && compressed_pages)
		cur_size = compressed_size;

	if (!extent_inserted) {
		struct btrfs_key key;
		size_t datasize;

		key.objectid = btrfs_ino(inode);
		key.offset = 0;
		key.type = BTRFS_EXTENT_DATA_KEY;

		datasize = btrfs_file_extent_calc_inline_size(cur_size);
		ret = btrfs_insert_empty_item(trans, root, path, &key,
					      datasize);
		if (ret)
			goto fail;
	}
	leaf = path->nodes[0];
	ei = btrfs_item_ptr(leaf, path->slots[0],
			    struct btrfs_file_extent_item);
	btrfs_set_file_extent_generation(leaf, ei, trans->transid);
	btrfs_set_file_extent_type(leaf, ei, BTRFS_FILE_EXTENT_INLINE);
	btrfs_set_file_extent_encryption(leaf, ei, 0);
	btrfs_set_file_extent_other_encoding(leaf, ei, 0);
	btrfs_set_file_extent_ram_bytes(leaf, ei, size);
	ptr = 