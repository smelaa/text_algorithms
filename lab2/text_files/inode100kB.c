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
	ptr = btrfs_file_extent_inline_start(ei);

	if (compress_type != BTRFS_COMPRESS_NONE) {
		struct page *cpage;
		int i = 0;
		while (compressed_size > 0) {
			cpage = compressed_pages[i];
			cur_size = min_t(unsigned long, compressed_size,
				       PAGE_SIZE);

			kaddr = kmap_local_page(cpage);
			write_extent_buffer(leaf, kaddr, ptr, cur_size);
			kunmap_local(kaddr);

			i++;
			ptr += cur_size;
			compressed_size -= cur_size;
		}
		btrfs_set_file_extent_compression(leaf, ei,
						  compress_type);
	} else {
		page = find_get_page(inode->vfs_inode.i_mapping, 0);
		btrfs_set_file_extent_compression(leaf, ei, 0);
		kaddr = kmap_local_page(page);
		write_extent_buffer(leaf, kaddr, ptr, size);
		kunmap_local(kaddr);
		put_page(page);
	}
	btrfs_mark_buffer_dirty(leaf);
	btrfs_release_path(path);

	/*
	 * We align size to sectorsize for inline extents just for simplicity
	 * sake.
	 */
	ret = btrfs_inode_set_file_extent_range(inode, 0,
					ALIGN(size, root->fs_info->sectorsize));
	if (ret)
		goto fail;

	/*
	 * We're an inline extent, so nobody can extend the file past i_size
	 * without locking a page we already have locked.
	 *
	 * We must do any i_size and inode updates before we unlock the pages.
	 * Otherwise we could end up racing with unlink.
	 */
	i_size = i_size_read(&inode->vfs_inode);
	if (update_i_size && size > i_size) {
		i_size_write(&inode->vfs_inode, size);
		i_size = size;
	}
	inode->disk_i_size = i_size;

fail:
	return ret;
}


/*
 * conditionally insert an inline extent into the file.  This
 * does the checks required to make sure the data is small enough
 * to fit as an inline extent.
 */
static noinline int cow_file_range_inline(struct btrfs_inode *inode, u64 size,
					  size_t compressed_size,
					  int compress_type,
					  struct page **compressed_pages,
					  bool update_i_size)
{
	struct btrfs_drop_extents_args drop_args = { 0 };
	struct btrfs_root *root = inode->root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_trans_handle *trans;
	u64 data_len = (compressed_size ?: size);
	int ret;
	struct btrfs_path *path;

	/*
	 * We can create an inline extent if it ends at or beyond the current
	 * i_size, is no larger than a sector (decompressed), and the (possibly
	 * compressed) data fits in a leaf and the configured maximum inline
	 * size.
	 */
	if (size < i_size_read(&inode->vfs_inode) ||
	    size > fs_info->sectorsize ||
	    data_len > BTRFS_MAX_INLINE_DATA_SIZE(fs_info) ||
	    data_len > fs_info->max_inline)
		return 1;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	trans = btrfs_join_transaction(root);
	if (IS_ERR(trans)) {
		btrfs_free_path(path);
		return PTR_ERR(trans);
	}
	trans->block_rsv = &inode->block_rsv;

	drop_args.path = path;
	drop_args.start = 0;
	drop_args.end = fs_info->sectorsize;
	drop_args.drop_cache = true;
	drop_args.replace_extent = true;
	drop_args.extent_item_size = btrfs_file_extent_calc_inline_size(data_len);
	ret = btrfs_drop_extents(trans, root, inode, &drop_args);
	if (ret) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	}

	ret = insert_inline_extent(trans, path, inode, drop_args.extent_inserted,
				   size, compressed_size, compress_type,
				   compressed_pages, update_i_size);
	if (ret && ret != -ENOSPC) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	} else if (ret == -ENOSPC) {
		ret = 1;
		goto out;
	}

	btrfs_update_inode_bytes(inode, size, drop_args.bytes_found);
	ret = btrfs_update_inode(trans, root, inode);
	if (ret && ret != -ENOSPC) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	} else if (ret == -ENOSPC) {
		ret = 1;
		goto out;
	}

	btrfs_set_inode_full_sync(inode);
out:
	/*
	 * Don't forget to free the reserved space, as for inlined extent
	 * it won't count as data extent, free them directly here.
	 * And at reserve time, it's always aligned to page size, so
	 * just free one page here.
	 */
	btrfs_qgroup_free_data(inode, NULL, 0, PAGE_SIZE);
	btrfs_free_path(path);
	btrfs_end_transaction(trans);
	return ret;
}

struct async_extent {
	u64 start;
	u64 ram_size;
	u64 compressed_size;
	struct page **pages;
	unsigned long nr_pages;
	int compress_type;
	struct list_head list;
};

struct async_chunk {
	struct btrfs_inode *inode;
	struct page *locked_page;
	u64 start;
	u64 end;
	blk_opf_t write_flags;
	struct list_head extents;
	struct cgroup_subsys_state *blkcg_css;
	struct btrfs_work work;
	struct async_cow *async_cow;
};

struct async_cow {
	atomic_t num_chunks;
	struct async_chunk chunks[];
};

static noinline int add_async_extent(struct async_chunk *cow,
				     u64 start, u64 ram_size,
				     u64 compressed_size,
				     struct page **pages,
				     unsigned long nr_pages,
				     int compress_type)
{
	struct async_extent *async_extent;

	async_extent = kmalloc(sizeof(*async_extent), GFP_NOFS);
	BUG_ON(!async_extent); /* -ENOMEM */
	async_extent->start = start;
	async_extent->ram_size = ram_size;
	async_extent->compressed_size = compressed_size;
	async_extent->pages = pages;
	async_extent->nr_pages = nr_pages;
	async_extent->compress_type = compress_type;
	list_add_tail(&async_extent->list, &cow->extents);
	return 0;
}

/*
 * Check if the inode needs to be submitted to compression, based on mount
 * options, defragmentation, properties or heuristics.
 */
static inline int inode_need_compress(struct btrfs_inode *inode, u64 start,
				      u64 end)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;

	if (!btrfs_inode_can_compress(inode)) {
		WARN(IS_ENABLED(CONFIG_BTRFS_DEBUG),
			KERN_ERR "BTRFS: unexpected compression for ino %llu\n",
			btrfs_ino(inode));
		return 0;
	}
	/*
	 * Special check for subpage.
	 *
	 * We lock the full page then run each delalloc range in the page, thus
	 * for the following case, we will hit some subpage specific corner case:
	 *
	 * 0		32K		64K
	 * |	|///////|	|///////|
	 *		\- A		\- B
	 *
	 * In above case, both range A and range B will try to unlock the full
	 * page [0, 64K), causing the one finished later will have page
	 * unlocked already, triggering various page lock requirement BUG_ON()s.
	 *
	 * So here we add an artificial limit that subpage compression can only
	 * if the range is fully page aligned.
	 *
	 * In theory we only need to ensure the first page is fully covered, but
	 * the tailing partial page will be locked until the full compression
	 * finishes, delaying the write of other range.
	 *
	 * TODO: Make btrfs_run_delalloc_range() to lock all delalloc range
	 * first to prevent any submitted async extent to unlock the full page.
	 * By this, we can ensure for subpage case that only the last async_cow
	 * will unlock the full page.
	 */
	if (fs_info->sectorsize < PAGE_SIZE) {
		if (!PAGE_ALIGNED(start) ||
		    !PAGE_ALIGNED(end + 1))
			return 0;
	}

	/* force compress */
	if (btrfs_test_opt(fs_info, FORCE_COMPRESS))
		return 1;
	/* defrag ioctl */
	if (inode->defrag_compress)
		return 1;
	/* bad compression ratios */
	if (inode->flags & BTRFS_INODE_NOCOMPRESS)
		return 0;
	if (btrfs_test_opt(fs_info, COMPRESS) ||
	    inode->flags & BTRFS_INODE_COMPRESS ||
	    inode->prop_compress)
		return btrfs_compress_heuristic(&inode->vfs_inode, start, end);
	return 0;
}

static inline void inode_should_defrag(struct btrfs_inode *inode,
		u64 start, u64 end, u64 num_bytes, u32 small_write)
{
	/* If this is a small write inside eof, kick off a defrag */
	if (num_bytes < small_write &&
	    (start > 0 || end + 1 < inode->disk_i_size))
		btrfs_add_inode_defrag(NULL, inode, small_write);
}

/*
 * we create compressed extents in two phases.  The first
 * phase compresses a range of pages that have already been
 * locked (both pages and state bits are locked).
 *
 * This is done inside an ordered work queue, and the compression
 * is spread across many cpus.  The actual IO submission is step
 * two, and the ordered work queue takes care of making sure that
 * happens in the same order things were put onto the queue by
 * writepages and friends.
 *
 * If this code finds it can't get good compression, it puts an
 * entry onto the work queue to write the uncompressed bytes.  This
 * makes sure that both compressed inodes and uncompressed inodes
 * are written in the same order that the flusher thread sent them
 * down.
 */
static noinline int compress_file_range(struct async_chunk *async_chunk)
{
	struct btrfs_inode *inode = async_chunk->inode;
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	u64 blocksize = fs_info->sectorsize;
	u64 start = async_chunk->start;
	u64 end = async_chunk->end;
	u64 actual_end;
	u64 i_size;
	int ret = 0;
	struct page **pages = NULL;
	unsigned long nr_pages;
	unsigned long total_compressed = 0;
	unsigned long total_in = 0;
	int i;
	int will_compress;
	int compress_type = fs_info->compress_type;
	int compressed_extents = 0;
	int redirty = 0;

	inode_should_defrag(inode, start, end, end - start + 1, SZ_16K);

	/*
	 * We need to save i_size before now because it could change in between
	 * us evaluating the size and assigning it.  This is because we lock and
	 * unlock the page in truncate and fallocate, and then modify the i_size
	 * later on.
	 *
	 * The barriers are to emulate READ_ONCE, remove that once i_size_read
	 * does that for us.
	 */
	barrier();
	i_size = i_size_read(&inode->vfs_inode);
	barrier();
	actual_end = min_t(u64, i_size, end + 1);
again:
	will_compress = 0;
	nr_pages = (end >> PAGE_SHIFT) - (start >> PAGE_SHIFT) + 1;
	nr_pages = min_t(unsigned long, nr_pages,
			BTRFS_MAX_COMPRESSED / PAGE_SIZE);

	/*
	 * we don't want to send crud past the end of i_size through
	 * compression, that's just a waste of CPU time.  So, if the
	 * end of the file is before the start of our current
	 * requested range of bytes, we bail out to the uncompressed
	 * cleanup code that can deal with all of this.
	 *
	 * It isn't really the fastest way to fix things, but this is a
	 * very uncommon corner.
	 */
	if (actual_end <= start)
		goto cleanup_and_bail_uncompressed;

	total_compressed = actual_end - start;

	/*
	 * Skip compression for a small file range(<=blocksize) that
	 * isn't an inline extent, since it doesn't save disk space at all.
	 */
	if (total_compressed <= blocksize &&
	   (start > 0 || end + 1 < inode->disk_i_size))
		goto cleanup_and_bail_uncompressed;

	/*
	 * For subpage case, we require full page alignment for the sector
	 * aligned range.
	 * Thus we must also check against @actual_end, not just @end.
	 */
	if (blocksize < PAGE_SIZE) {
		if (!PAGE_ALIGNED(start) ||
		    !PAGE_ALIGNED(round_up(actual_end, blocksize)))
			goto cleanup_and_bail_uncompressed;
	}

	total_compressed = min_t(unsigned long, total_compressed,
			BTRFS_MAX_UNCOMPRESSED);
	total_in = 0;
	ret = 0;

	/*
	 * we do compression for mount -o compress and when the
	 * inode has not been flagged as nocompress.  This flag can
	 * change at any time if we discover bad compression ratios.
	 */
	if (inode_need_compress(inode, start, end)) {
		WARN_ON(pages);
		pages = kcalloc(nr_pages, sizeof(struct page *), GFP_NOFS);
		if (!pages) {
			/* just bail out to the uncompressed code */
			nr_pages = 0;
			goto cont;
		}

		if (inode->defrag_compress)
			compress_type = inode->defrag_compress;
		else if (inode->prop_compress)
			compress_type = inode->prop_compress;

		/*
		 * we need to call clear_page_dirty_for_io on each
		 * page in the range.  Otherwise applications with the file
		 * mmap'd can wander in and change the page contents while
		 * we are compressing them.
		 *
		 * If the compression fails for any reason, we set the pages
		 * dirty again later on.
		 *
		 * Note that the remaining part is redirtied, the start pointer
		 * has moved, the end is the original one.
		 */
		if (!redirty) {
			extent_range_clear_dirty_for_io(&inode->vfs_inode, start, end);
			redirty = 1;
		}

		/* Compression level is applied here and only here */
		ret = btrfs_compress_pages(
			compress_type | (fs_info->compress_level << 4),
					   inode->vfs_inode.i_mapping, start,
					   pages,
					   &nr_pages,
					   &total_in,
					   &total_compressed);

		if (!ret) {
			unsigned long offset = offset_in_page(total_compressed);
			struct page *page = pages[nr_pages - 1];

			/* zero the tail end of the last page, we might be
			 * sending it down to disk
			 */
			if (offset)
				memzero_page(page, offset, PAGE_SIZE - offset);
			will_compress = 1;
		}
	}
cont:
	/*
	 * Check cow_file_range() for why we don't even try to create inline
	 * extent for subpage case.
	 */
	if (start == 0 && fs_info->sectorsize == PAGE_SIZE) {
		/* lets try to make an inline extent */
		if (ret || total_in < actual_end) {
			/* we didn't compress the entire range, try
			 * to make an uncompressed inline extent.
			 */
			ret = cow_file_range_inline(inode, actual_end,
						    0, BTRFS_COMPRESS_NONE,
						    NULL, false);
		} else {
			/* try making a compressed inline extent */
			ret = cow_file_range_inline(inode, actual_end,
						    total_compressed,
						    compress_type, pages,
						    false);
		}
		if (ret <= 0) {
			unsigned long clear_flags = EXTENT_DELALLOC |
				EXTENT_DELALLOC_NEW | EXTENT_DEFRAG |
				EXTENT_DO_ACCOUNTING;
			unsigned long page_error_op;

			page_error_op = ret < 0 ? PAGE_SET_ERROR : 0;

			/*
			 * inline extent creation worked or returned error,
			 * we don't need to create any more async work items.
			 * Unlock and free up our temp pages.
			 *
			 * We use DO_ACCOUNTING here because we need the
			 * delalloc_release_metadata to be done _after_ we drop
			 * our outstanding extent for clearing delalloc for this
			 * range.
			 */
			extent_clear_unlock_delalloc(inode, start, end,
						     NULL,
						     clear_flags,
						     PAGE_UNLOCK |
						     PAGE_START_WRITEBACK |
						     page_error_op |
						     PAGE_END_WRITEBACK);

			/*
			 * Ensure we only free the compressed pages if we have
			 * them allocated, as we can still reach here with
			 * inode_need_compress() == false.
			 */
			if (pages) {
				for (i = 0; i < nr_pages; i++) {
					WARN_ON(pages[i]->mapping);
					put_page(pages[i]);
				}
				kfree(pages);
			}
			return 0;
		}
	}

	if (will_compress) {
		/*
		 * we aren't doing an inline extent round the compressed size
		 * up to a block size boundary so the allocator does sane
		 * things
		 */
		total_compressed = ALIGN(total_compressed, blocksize);

		/*
		 * one last check to make sure the compression is really a
		 * win, compare the page count read with the blocks on disk,
		 * compression must free at least one sector size
		 */
		total_in = round_up(total_in, fs_info->sectorsize);
		if (total_compressed + blocksize <= total_in) {
			compressed_extents++;

			/*
			 * The async work queues will take care of doing actual
			 * allocation on disk for these compressed pages, and
			 * will submit them to the elevator.
			 */
			add_async_extent(async_chunk, start, total_in,
					total_compressed, pages, nr_pages,
					compress_type);

			if (start + total_in < end) {
				start += total_in;
				pages = NULL;
				cond_resched();
				goto again;
			}
			return compressed_extents;
		}
	}
	if (pages) {
		/*
		 * the compression code ran but failed to make things smaller,
		 * free any pages it allocated and our page pointer array
		 */
		for (i = 0; i < nr_pages; i++) {
			WARN_ON(pages[i]->mapping);
			put_page(pages[i]);
		}
		kfree(pages);
		pages = NULL;
		total_compressed = 0;
		nr_pages = 0;

		/* flag the file so we don't compress in the future */
		if (!btrfs_test_opt(fs_info, FORCE_COMPRESS) &&
		    !(inode->prop_compress)) {
			inode->flags |= BTRFS_INODE_NOCOMPRESS;
		}
	}
cleanup_and_bail_uncompressed:
	/*
	 * No compression, but we still need to write the pages in the file
	 * we've been given so far.  redirty the locked page if it corresponds
	 * to our extent and set things up for the async work queue to run
	 * cow_file_range to do the normal delalloc dance.
	 */
	if (async_chunk->locked_page &&
	    (page_offset(async_chunk->locked_page) >= start &&
	     page_offset(async_chunk->locked_page)) <= end) {
		__set_page_dirty_nobuffers(async_chunk->locked_page);
		/* unlocked later on in the async handlers */
	}

	if (redirty)
		extent_range_redirty_for_io(&inode->vfs_inode, start, end);
	add_async_extent(async_chunk, start, end - start + 1, 0, NULL, 0,
			 BTRFS_COMPRESS_NONE);
	compressed_extents++;

	return compressed_extents;
}

static void free_async_extent_pages(struct async_extent *async_extent)
{
	int i;

	if (!async_extent->pages)
		return;

	for (i = 0; i < async_extent->nr_pages; i++) {
		WARN_ON(async_extent->pages[i]->mapping);
		put_page(async_extent->pages[i]);
	}
	kfree(async_extent->pages);
	async_extent->nr_pages = 0;
	async_extent->pages = NULL;
}

static int submit_uncompressed_range(struct btrfs_inode *inode,
				     struct async_extent *async_extent,
				     struct page *locked_page)
{
	u64 start = async_extent->start;
	u64 end = async_extent->start + async_extent->ram_size - 1;
	unsigned long nr_written = 0;
	int page_started = 0;
	int ret;

	/*
	 * Call cow_file_range() to run the delalloc range directly, since we
	 * won't go to NOCOW or async path again.
	 *
	 * Also we call cow_file_range() with @unlock_page == 0, so that we
	 * can directly submit them without interruption.
	 */
	ret = cow_file_range(inode, locked_page, start, end, &page_started,
			     &nr_written, 0, NULL);
	/* Inline extent inserted, page gets unlocked and everything is done */
	if (page_started) {
		ret = 0;
		goto out;
	}
	if (ret < 0) {
		btrfs_cleanup_ordered_extents(inode, locked_page, start, end - start + 1);
		if (locked_page) {
			const u64 page_start = page_offset(locked_page);
			const u64 page_end = page_start + PAGE_SIZE - 1;

			btrfs_page_set_error(inode->root->fs_info, locked_page,
					     page_start, PAGE_SIZE);
			set_page_writeback(locked_page);
			end_page_writeback(locked_page);
			end_extent_writepage(locked_page, ret, page_start, page_end);
			unlock_page(locked_page);
		}
		goto out;
	}

	ret = extent_write_locked_range(&inode->vfs_inode, start, end);
	/* All pages will be unlocked, including @locked_page */
out:
	kfree(async_extent);
	return ret;
}

static int submit_one_async_extent(struct btrfs_inode *inode,
				   struct async_chunk *async_chunk,
				   struct async_extent *async_extent,
				   u64 *alloc_hint)
{
	struct extent_io_tree *io_tree = &inode->io_tree;
	struct btrfs_root *root = inode->root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_key ins;
	struct page *locked_page = NULL;
	struct extent_map *em;
	int ret = 0;
	u64 start = async_extent->start;
	u64 end = async_extent->start + async_extent->ram_size - 1;

	/*
	 * If async_chunk->locked_page is in the async_extent range, we need to
	 * handle it.
	 */
	if (async_chunk->locked_page) {
		u64 locked_page_start = page_offset(async_chunk->locked_page);
		u64 locked_page_end = locked_page_start + PAGE_SIZE - 1;

		if (!(start >= locked_page_end || end <= locked_page_start))
			locked_page = async_chunk->locked_page;
	}
	lock_extent(io_tree, start, end, NULL);

	/* We have fall back to uncompressed write */
	if (!async_extent->pages)
		return submit_uncompressed_range(inode, async_extent, locked_page);

	ret = btrfs_reserve_extent(root, async_extent->ram_size,
				   async_extent->compressed_size,
				   async_extent->compressed_size,
				   0, *alloc_hint, &ins, 1, 1);
	if (ret) {
		free_async_extent_pages(async_extent);
		/*
		 * Here we used to try again by going back to non-compressed
		 * path for ENOSPC.  But we can't reserve space even for
		 * compressed size, how could it work for uncompressed size
		 * which requires larger size?  So here we directly go error
		 * path.
		 */
		goto out_free;
	}

	/* Here we're doing allocation and writeback of the compressed pages */
	em = create_io_em(inode, start,
			  async_extent->ram_size,	/* len */
			  start,			/* orig_start */
			  ins.objectid,			/* block_start */
			  ins.offset,			/* block_len */
			  ins.offset,			/* orig_block_len */
			  async_extent->ram_size,	/* ram_bytes */
			  async_extent->compress_type,
			  BTRFS_ORDERED_COMPRESSED);
	if (IS_ERR(em)) {
		ret = PTR_ERR(em);
		goto out_free_reserve;
	}
	free_extent_map(em);

	ret = btrfs_add_ordered_extent(inode, start,		/* file_offset */
				       async_extent->ram_size,	/* num_bytes */
				       async_extent->ram_size,	/* ram_bytes */
				       ins.objectid,		/* disk_bytenr */
				       ins.offset,		/* disk_num_bytes */
				       0,			/* offset */
				       1 << BTRFS_ORDERED_COMPRESSED,
				       async_extent->compress_type);
	if (ret) {
		btrfs_drop_extent_map_range(inode, start, end, false);
		goto out_free_reserve;
	}
	btrfs_dec_block_group_reservations(fs_info, ins.objectid);

	/* Clear dirty, set writeback and unlock the pages. */
	extent_clear_unlock_delalloc(inode, start, end,
			NULL, EXTENT_LOCKED | EXTENT_DELALLOC,
			PAGE_UNLOCK | PAGE_START_WRITEBACK);
	if (btrfs_submit_compressed_write(inode, start,	/* file_offset */
			    async_extent->ram_size,	/* num_bytes */
			    ins.objectid,		/* disk_bytenr */
			    ins.offset,			/* compressed_len */
			    async_extent->pages,	/* compressed_pages */
			    async_extent->nr_pages,
			    async_chunk->write_flags,
			    async_chunk->blkcg_css, true)) {
		const u64 start = async_extent->start;
		const u64 end = start + async_extent->ram_size - 1;

		btrfs_writepage_endio_finish_ordered(inode, NULL, start, end, 0);

		extent_clear_unlock_delalloc(inode, start, end, NULL, 0,
					     PAGE_END_WRITEBACK | PAGE_SET_ERROR);
		free_async_extent_pages(async_extent);
	}
	*alloc_hint = ins.objectid + ins.offset;
	kfree(async_extent);
	return ret;

out_free_reserve:
	btrfs_dec_block_group_reservations(fs_info, ins.objectid);
	btrfs_free_reserved_extent(fs_info, ins.objectid, ins.offset, 1);
out_free:
	extent_clear_unlock_delalloc(inode, start, end,
				     NULL, EXTENT_LOCKED | EXTENT_DELALLOC |
				     EXTENT_DELALLOC_NEW |
				     EXTENT_DEFRAG | EXTENT_DO_ACCOUNTING,
				     PAGE_UNLOCK | PAGE_START_WRITEBACK |
				     PAGE_END_WRITEBACK | PAGE_SET_ERROR);
	free_async_extent_pages(async_extent);
	kfree(async_extent);
	return ret;
}

/*
 * Phase two of compressed writeback.  This is the ordered portion of the code,
 * which only gets called in the order the work was queued.  We walk all the
 * async extents created by compress_file_range and send them down to the disk.
 */
static noinline void submit_compressed_extents(struct async_chunk *async_chunk)
{
	struct btrfs_inode *inode = async_chunk->inode;
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	struct async_extent *async_extent;
	u64 alloc_hint = 0;
	int ret = 0;

	while (!list_empty(&async_chunk->extents)) {
		u64 extent_start;
		u64 ram_size;

		async_extent = list_entry(async_chunk->extents.next,
					  struct async_extent, list);
		list_del(&async_extent->list);
		extent_start = async_extent->start;
		ram_size = async_extent->ram_size;

		ret = submit_one_async_extent(inode, async_chunk, async_extent,
					      &alloc_hint);
		btrfs_debug(fs_info,
"async extent submission failed root=%lld inode=%llu start=%llu len=%llu ret=%d",
			    inode->root->root_key.objectid,
			    btrfs_ino(inode), extent_start, ram_size, ret);
	}
}

static u64 get_extent_allocation_hint(struct btrfs_inode *inode, u64 start,
				      u64 num_bytes)
{
	struct extent_map_tree *em_tree = &inode->extent_tree;
	struct extent_map *em;
	u64 alloc_hint = 0;

	read_lock(&em_tree->lock);
	em = search_extent_mapping(em_tree, start, num_bytes);
	if (em) {
		/*
		 * if block start isn't an actual block number then find the
		 * first block in this inode and use that as a hint.  If that
		 * block is also bogus then just don't worry about it.
		 */
		if (em->block_start >= EXTENT_MAP_LAST_BYTE) {
			free_extent_map(em);
			em = search_extent_mapping(em_tree, 0, 0);
			if (em && em->block_start < EXTENT_MAP_LAST_BYTE)
				alloc_hint = em->block_start;
			if (em)
				free_extent_map(em);
		} else {
			alloc_hint = em->block_start;
			free_extent_map(em);
		}
	}
	read_unlock(&em_tree->lock);

	return alloc_hint;
}

/*
 * when extent_io.c finds a delayed allocation range in the file,
 * the call backs end up in this code.  The basic idea is to
 * allocate extents on disk for the range, and create ordered data structs
 * in ram to track those extents.
 *
 * locked_page is the page that writepage had locked already.  We use
 * it to make sure we don't do extra locks or unlocks.
 *
 * *page_started is set to one if we unlock locked_page and do everything
 * required to start IO on it.  It may be clean and already done with
 * IO when we return.
 *
 * When unlock == 1, we unlock the pages in successfully allocated regions.
 * When unlock == 0, we leave them locked for writing them out.
 *
 * However, we unlock all the pages except @locked_page in case of failure.
 *
 * In summary, page locking state will be as follow:
 *
 * - page_started == 1 (return value)
 *     - All the pages are unlocked. IO is started.
 *     - Note that this can happen only on success
 * - unlock == 1
 *     - All the pages except @locked_page are unlocked in any case
 * - unlock == 0
 *     - On success, all the pages are locked for writing out them
 *     - On failure, all the pages except @locked_page are unlocked
 *
 * When a failure happens in the second or later iteration of the
 * while-loop, the ordered extents created in previous iterations are kept
 * intact. So, the caller must clean them up by calling
 * btrfs_cleanup_ordered_extents(). See btrfs_run_delalloc_range() for
 * example.
 */
static noinline int cow_file_range(struct btrfs_inode *inode,
				   struct page *locked_page,
				   u64 start, u64 end, int *page_started,
				   unsigned long *nr_written, int unlock,
				   u64 *done_offset)
{
	struct btrfs_root *root = inode->root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	u64 alloc_hint = 0;
	u64 orig_start = start;
	u64 num_bytes;
	unsigned long ram_size;
	u64 cur_alloc_size = 0;
	u64 min_alloc_size;
	u64 blocksize = fs_info->sectorsize;
	struct btrfs_key ins;
	struct extent_map *em;
	unsigned clear_bits;
	unsigned long page_ops;
	bool extent_reserved = false;
	int ret = 0;

	if (btrfs_is_free_space_inode(inode)) {
		ret = -EINVAL;
		goto out_unlock;
	}

	num_bytes = ALIGN(end - start + 1, blocksize);
	num_bytes = max(blocksize,  num_bytes);
	ASSERT(num_bytes <= btrfs_super_total_bytes(fs_info->super_copy));

	inode_should_defrag(inode, start, end, num_bytes, SZ_64K);

	/*
	 * Due to the page size limit, for subpage we can only trigger the
	 * writeback for the dirty sectors of page, that means data writeback
	 * is doing more writeback than what we want.
	 *
	 * This is especially unexpected for some call sites like fallocate,
	 * where we only increase i_size after everything is done.
	 * This means we can trigger inline extent even if we didn't want to.
	 * So here we skip inline extent creation completely.
	 */
	if (start == 0 && fs_info->sectorsize == PAGE_SIZE) {
		u64 actual_end = min_t(u64, i_size_read(&inode->vfs_inode),
				       end + 1);

		/* lets try to make an inline extent */
		ret = cow_file_range_inline(inode, actual_end, 0,
					    BTRFS_COMPRESS_NONE, NULL, false);
		if (ret == 0) {
			/*
			 * We use DO_ACCOUNTING here because we need the
			 * delalloc_release_metadata to be run _after_ we drop
			 * our outstanding extent for clearing delalloc for this
			 * range.
			 */
			extent_clear_unlock_delalloc(inode, start, end,
				     locked_page,
				     EXTENT_LOCKED | EXTENT_DELALLOC |
				     EXTENT_DELALLOC_NEW | EXTENT_DEFRAG |
				     EXTENT_DO_ACCOUNTING, PAGE_UNLOCK |
				     PAGE_START_WRITEBACK | PAGE_END_WRITEBACK);
			*nr_written = *nr_written +
			     (end - start + PAGE_SIZE) / PAGE_SIZE;
			*page_started = 1;
			/*
			 * locked_page is locked by the caller of
			 * writepage_delalloc(), not locked by
			 * __process_pages_contig().
			 *
			 * We can't let __process_pages_contig() to unlock it,
			 * as it doesn't have any subpage::writers recorded.
			 *
			 * Here we manually unlock the page, since the caller
			 * can't use page_started to determine if it's an
			 * inline extent or a compressed extent.
			 */
			unlock_page(locked_page);
			goto out;
		} else if (ret < 0) {
			goto out_unlock;
		}
	}

	alloc_hint = get_extent_allocation_hint(inode, start, num_bytes);

	/*
	 * Relocation relies on the relocated extents to have exactly the same
	 * size as the original extents. Normally writeback for relocation data
	 * extents follows a NOCOW path because relocation preallocates the
	 * extents. However, due to an operation such as scrub turning a block
	 * group to RO mode, it may fallback to COW mode, so we must make sure
	 * an extent allocated during COW has exactly the requested size and can
	 * not be split into smaller extents, otherwise relocation breaks and
	 * fails during the stage where it updates the bytenr of file extent
	 * items.
	 */
	if (btrfs_is_data_reloc_root(root))
		min_alloc_size = num_bytes;
	else
		min_alloc_size = fs_info->sectorsize;

	while (num_bytes > 0) {
		cur_alloc_size = num_bytes;
		ret = btrfs_reserve_extent(root, cur_alloc_size, cur_alloc_size,
					   min_alloc_size, 0, alloc_hint,
					   &ins, 1, 1);
		if (ret < 0)
			goto out_unlock;
		cur_alloc_size = ins.offset;
		extent_reserved = true;

		ram_size = ins.offset;
		em = create_io_em(inode, start, ins.offset, /* len */
				  start, /* orig_start */
				  ins.objectid, /* block_start */
				  ins.offset, /* block_len */
				  ins.offset, /* orig_block_len */
				  ram_size, /* ram_bytes */
				  BTRFS_COMPRESS_NONE, /* compress_type */
				  BTRFS_ORDERED_REGULAR /* type */);
		if (IS_ERR(em)) {
			ret = PTR_ERR(em);
			goto out_reserve;
		}
		free_extent_map(em);

		ret = btrfs_add_ordered_extent(inode, start, ram_size, ram_size,
					       ins.objectid, cur_alloc_size, 0,
					       1 << BTRFS_ORDERED_REGULAR,
					       BTRFS_COMPRESS_NONE);
		if (ret)
			goto out_drop_extent_cache;

		if (btrfs_is_data_reloc_root(root)) {
			ret = btrfs_reloc_clone_csums(inode, start,
						      cur_alloc_size);
			/*
			 * Only drop cache here, and process as normal.
			 *
			 * We must not allow extent_clear_unlock_delalloc()
			 * at out_unlock label to free meta of this ordered
			 * extent, as its meta should be freed by
			 * btrfs_finish_ordered_io().
			 *
			 * So we must continue until @start is increased to
			 * skip current ordered extent.
			 */
			if (ret)
				btrfs_drop_extent_map_range(inode, start,
							    start + ram_size - 1,
							    false);
		}

		btrfs_dec_block_group_reservations(fs_info, ins.objectid);

		/*
		 * We're not doing compressed IO, don't unlock the first page
		 * (which the caller expects to stay locked), don't clear any
		 * dirty bits and don't set any writeback bits
		 *
		 * Do set the Ordered (Private2) bit so we know this page was
		 * properly setup for writepage.
		 */
		page_ops = unlock ? PAGE_UNLOCK : 0;
		page_ops |= PAGE_SET_ORDERED;

		extent_clear_unlock_delalloc(inode, start, start + ram_size - 1,
					     locked_page,
					     EXTENT_LOCKED | EXTENT_DELALLOC,
					     page_ops);
		if (num_bytes < cur_alloc_size)
			num_bytes = 0;
		else
			num_bytes -= cur_alloc_size;
		alloc_hint = ins.objectid + ins.offset;
		start += cur_alloc_size;
		extent_reserved = false;

		/*
		 * btrfs_reloc_clone_csums() error, since start is increased
		 * extent_clear_unlock_delalloc() at out_unlock label won't
		 * free metadata of current ordered extent, we're OK to exit.
		 */
		if (ret)
			goto out_unlock;
	}
out:
	return ret;

out_drop_extent_cache:
	btrfs_drop_extent_map_range(inode, start, start + ram_size - 1, false);
out_reserve:
	btrfs_dec_block_group_reservations(fs_info, ins.objectid);
	btrfs_free_reserved_extent(fs_info, ins.objectid, ins.offset, 1);
out_unlock:
	/*
	 * If done_offset is non-NULL and ret == -EAGAIN, we expect the
	 * caller to write out the successfully allocated region and retry.
	 */
	if (done_offset && ret == -EAGAIN) {
		if (orig_start < start)
			*done_offset = start - 1;
		else
			*done_offset = start;
		return ret;
	} else if (ret == -EAGAIN) {
		/* Convert to -ENOSPC since the caller cannot retry. */
		ret = -ENOSPC;
	}

	/*
	 * Now, we have three regions to clean up:
	 *
	 * |-------(1)----|---(2)---|-------------(3)----------|
	 * `- orig_start  `- start  `- start + cur_alloc_size  `- end
	 *
	 * We process each region below.
	 */

	clear_bits = EXTENT_LOCKED | EXTENT_DELALLOC | EXTENT_DELALLOC_NEW |
		EXTENT_DEFRAG | EXTENT_CLEAR_META_RESV;
	page_ops = PAGE_UNLOCK | PAGE_START_WRITEBACK | PAGE_END_WRITEBACK;

	/*
	 * For the range (1). We have already instantiated the ordered extents
	 * for this region. They are cleaned up by
	 * btrfs_cleanup_ordered_extents() in e.g,
	 * btrfs_run_delalloc_range(). EXTENT_LOCKED | EXTENT_DELALLOC are
	 * already cleared in the above loop. And, EXTENT_DELALLOC_NEW |
	 * EXTENT_DEFRAG | EXTENT_CLEAR_META_RESV are handled by the cleanup
	 * function.
	 *
	 * However, in case of unlock == 0, we still need to unlock the pages
	 * (except @locked_page) to ensure all the pages are unlocked.
	 */
	if (!unlock && orig_start < start) {
		if (!locked_page)
			mapping_set_error(inode->vfs_inode.i_mapping, ret);
		extent_clear_unlock_delalloc(inode, orig_start, start - 1,
					     locked_page, 0, page_ops);
	}

	/*
	 * For the range (2). If we reserved an extent for our delalloc range
	 * (or a subrange) and failed to create the respective ordered extent,
	 * then it means that when we reserved the extent we decremented the
	 * extent's size from the data space_info's bytes_may_use counter and
	 * incremented the space_info's bytes_reserved counter by the same
	 * amount. We must make sure extent_clear_unlock_delalloc() does not try
	 * to decrement again the data space_info's bytes_may_use counter,
	 * therefore we do not pass it the flag EXTENT_CLEAR_DATA_RESV.
	 */
	if (extent_reserved) {
		extent_clear_unlock_delalloc(inode, start,
					     start + cur_alloc_size - 1,
					     locked_page,
					     clear_bits,
					     page_ops);
		start += cur_alloc_size;
		if (start >= end)
			return ret;
	}

	/*
	 * For the range (3). We never touched the region. In addition to the
	 * clear_bits above, we add EXTENT_CLEAR_DATA_RESV to release the data
	 * space_info's bytes_may_use counter, reserved in
	 * btrfs_check_data_free_space().
	 */
	extent_clear_unlock_delalloc(inode, start, end, locked_page,
				     clear_bits | EXTENT_CLEAR_DATA_RESV,
				     page_ops);
	return ret;
}

/*
 * work queue call back to started compression on a file and pages
 */
static noinline void async_cow_start(struct btrfs_work *work)
{
	struct async_chunk *async_chunk;
	int compressed_extents;

	async_chunk = container_of(work, struct async_chunk, work);

	compressed_extents = compress_file_range(async_chunk);
	if (compressed_extents == 0) {
		btrfs_add_delayed_iput(async_chunk->inode);
		async_chunk->inode = NULL;
	}
}

/*
 * work queue call back to submit previously compressed pages
 */
static noinline void async_cow_submit(struct btrfs_work *work)
{
	struct async_chunk *async_chunk = container_of(work, struct async_chunk,
						     work);
	struct btrfs_fs_info *fs_info = btrfs_work_owner(work);
	unsigned long nr_pages;

	nr_pages = (async_chunk->end - async_chunk->start + PAGE_SIZE) >>
		PAGE_SHIFT;

	/*
	 * ->inode could be NULL if async_chunk_start has failed to compress,
	 * in which case we don't have anything to submit, yet we need to
	 * always adjust ->async_delalloc_pages as its paired with the init
	 * happening in cow_file_range_async
	 */
	if (async_chunk->inode)
		submit_compressed_extents(async_chunk);

	/* atomic_sub_return implies a barrier */
	if (atomic_sub_return(nr_pages, &fs_info->async_delalloc_pages) <
	    5 * SZ_1M)
		cond_wake_up_nomb(&fs_info->async_submit_wait);
}

static noinline void async_cow_free(struct btrfs_work *work)
{
	struct async_chunk *async_chunk;
	struct async_cow *async_cow;

	async_chunk = container_of(work, struct async_chunk, work);
	if (async_chunk->inode)
		btrfs_add_delayed_iput(async_chunk->inode);
	if (async_chunk->blkcg_css)
		css_put(async_chunk->blkcg_css);

	async_cow = async_chunk->async_cow;
	if (atomic_dec_and_test(&async_cow->num_chunks))
		kvfree(async_cow);
}

static int cow_file_range_async(struct btrfs_inode *inode,
				struct writeback_control *wbc,
				struct page *locked_page,
				u64 start, u64 end, int *page_started,
				unsigned long *nr_written)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	struct cgroup_subsys_state *blkcg_css = wbc_blkcg_css(wbc);
	struct async_cow *ctx;
	struct async_chunk *async_chunk;
	unsigned long nr_pages;
	u64 cur_end;
	u64 num_chunks = DIV_ROUND_UP(end - start, SZ_512K);
	int i;
	bool should_compress;
	unsigned nofs_flag;
	const blk_opf_t write_flags = wbc_to_write_flags(wbc);

	unlock_extent(&inode->io_tree, start, end, NULL);

	if (inode->flags & BTRFS_INODE_NOCOMPRESS &&
	    !btrfs_test_opt(fs_info, FORCE_COMPRESS)) {
		num_chunks = 1;
		should_compress = false;
	} else {
		should_compress = true;
	}

	nofs_flag = memalloc_nofs_save();
	ctx = kvmalloc(struct_size(ctx, chunks, num_chunks), GFP_KERNEL);
	memalloc_nofs_restore(nofs_flag);

	if (!ctx) {
		unsigned clear_bits = EXTENT_LOCKED | EXTENT_DELALLOC |
			EXTENT_DELALLOC_NEW | EXTENT_DEFRAG |
			EXTENT_DO_ACCOUNTING;
		unsigned long page_ops = PAGE_UNLOCK | PAGE_START_WRITEBACK |
					 PAGE_END_WRITEBACK | PAGE_SET_ERROR;

		extent_clear_unlock_delalloc(inode, start, end, locked_page,
					     clear_bits, page_ops);
		return -ENOMEM;
	}

	async_chunk = ctx->chunks;
	atomic_set(&ctx->num_chunks, num_chunks);

	for (i = 0; i < num_chunks; i++) {
		if (should_compress)
			cur_end = min(end, start + SZ_512K - 1);
		else
			cur_end = end;

		/*
		 * igrab is called higher up in the call chain, take only the
		 * lightweight reference for the callback lifetime
		 */
		ihold(&inode->vfs_inode);
		async_chunk[i].async_cow = ctx;
		async_chunk[i].inode = inode;
		async_chunk[i].start = start;
		async_chunk[i].end = cur_end;
		async_chunk[i].write_flags = write_flags;
		INIT_LIST_HEAD(&async_chunk[i].extents);

		/*
		 * The locked_page comes all the way from writepage and its
		 * the original page we were actually given.  As we spread
		 * this large delalloc region across multiple async_chunk
		 * structs, only the first struct needs a pointer to locked_page
		 *
		 * This way we don't need racey decisions about who is supposed
		 * to unlock it.
		 */
		if (locked_page) {
			/*
			 * Depending on the compressibility, the pages might or
			 * might not go through async.  We want all of them to
			 * be accounted against wbc once.  Let's do it here
			 * before the paths diverge.  wbc accounting is used
			 * only for foreign writeback detection and doesn't
			 * need full accuracy.  Just account the whole thing
			 * against the first page.
			 */
			wbc_account_cgroup_owner(wbc, locked_page,
						 cur_end - start);
			async_chunk[i].locked_page = locked_page;
			locked_page = NULL;
		} else {
			async_chunk[i].locked_page = NULL;
		}

		if (blkcg_css != blkcg_root_css) {
			css_get(blkcg_css);
			async_chunk[i].blkcg_css = blkcg_css;
		} else {
			async_chunk[i].blkcg_css = NULL;
		}

		btrfs_init_work(&async_chunk[i].work, async_cow_start,
				async_cow_submit, async_cow_free);

		nr_pages = DIV_ROUND_UP(cur_end - start, PAGE_SIZE);
		atomic_add(nr_pages, &fs_info->async_delalloc_pages);

		btrfs_queue_work(fs_info->delalloc_workers, &async_chunk[i].work);

		*nr_written += nr_pages;
		start = cur_end + 1;
	}
	*page_started = 1;
	return 0;
}

static noinline int run_delalloc_zoned(struct btrfs_inode *inode,
				       struct page *locked_page, u64 start,
				       u64 end, int *page_started,
				       unsigned long *nr_written)
{
	u64 done_offset = end;
	int ret;
	bool locked_page_done = false;

	while (start <= end) {
		ret = cow_file_range(inode, locked_page, start, end, page_started,
				     nr_written, 0, &done_offset);
		if (ret && ret != -EAGAIN)
			return ret;

		if (*page_started) {
			ASSERT(ret == 0);
			return 0;
		}

		if (ret == 0)
			done_offset = end;

		if (done_offset == start) {
			wait_on_bit_io(&inode->root->fs_info->flags,
				       BTRFS_FS_NEED_ZONE_FINISH,
				       TASK_UNINTERRUPTIBLE);
			continue;
		}

		if (!locked_page_done) {
			__set_page_dirty_nobuffers(locked_page);
			account_page_redirty(locked_page);
		}
		locked_page_done = true;
		extent_write_locked_range(&inode->vfs_inode, start, done_offset);

		start = done_offset + 1;
	}

	*page_started = 1;

	return 0;
}

static noinline int csum_exist_in_range(struct btrfs_fs_info *fs_info,
					u64 bytenr, u64 num_bytes, bool nowait)
{
	struct btrfs_root *csum_root = btrfs_csum_root(fs_info, bytenr);
	struct btrfs_ordered_sum *sums;
	int ret;
	LIST_HEAD(list);

	ret = btrfs_lookup_csums_list(csum_root, bytenr, bytenr + num_bytes - 1,
				      &list, 0, nowait);
	if (ret == 0 && list_empty(&list))
		return 0;

	while (!list_empty(&list)) {
		sums = list_entry(list.next, struct btrfs_ordered_sum, list);
		list_del(&sums->list);
		kfree(sums);
	}
	if (ret < 0)
		return ret;
	return 1;
}

static int fallback_to_cow(struct btrfs_inode *inode, struct page *locked_page,
			   const u64 start, const u64 end,
			   int *page_started, unsigned long *nr_written)
{
	const bool is_space_ino = btrfs_is_free_space_inode(inode);
	const bool is_reloc_ino = btrfs_is_data_reloc_root(inode->root);
	const u64 range_bytes = end + 1 - start;
	struct extent_io_tree *io_tree = &inode->io_tree;
	u64 range_start = start;
	u64 count;

	/*
	 * If EXTENT_NORESERVE is set it means that when the buffered write was
	 * made we had not enough available data space and therefore we did not
	 * reserve data space for it, since we though we could do NOCOW for the
	 * respective file range (either there is prealloc extent or the inode
	 * has the NOCOW bit set).
	 *
	 * However when we need to fallback to COW mode (because for example the
	 * block group for the corresponding extent was turned to RO mode by a
	 * scrub or relocation) we need to do the following:
	 *
	 * 1) We increment the bytes_may_use counter of the data space info.
	 *    If COW succeeds, it allocates a new data extent and after doing
	 *    that it decrements the space info's bytes_may_use counter and
	 *    increments its bytes_reserved counter by the same amount (we do
	 *    this at btrfs_add_reserved_bytes()). So we need to increment the
	 *    bytes_may_use counter to compensate (when space is reserved at
	 *    buffered write time, the bytes_may_use counter is incremented);
	 *
	 * 2) We clear the EXTENT_NORESERVE bit from the range. We do this so
	 *    that if the COW path fails for any reason, it decrements (through
	 *    extent_clear_unlock_delalloc()) the bytes_may_use counter of the
	 *    data space info, which we incremented in the step above.
	 *
	 * If we need to fallback to cow and the inode corresponds to a free
	 * space cache inode or an inode of the data relocation tree, we must
	 * also increment bytes_may_use of the data space_info for the same
	 * reason. Space caches and relocated data extents always get a prealloc
	 * extent for them, however scrub or balance may have set the block
	 * group that contains that extent to RO mode and therefore force COW
	 * when starting writeback.
	 */
	count = count_range_bits(io_tree, &range_start, end, range_bytes,
				 EXTENT_NORESERVE, 0, NULL);
	if (count > 0 || is_space_ino || is_reloc_ino) {
		u64 bytes = count;
		struct btrfs_fs_info *fs_info = inode->root->fs_info;
		struct btrfs_space_info *sinfo = fs_info->data_sinfo;

		if (is_space_ino || is_reloc_ino)
			bytes = range_bytes;

		spin_lock(&sinfo->lock);
		btrfs_space_info_update_bytes_may_use(fs_info, sinfo, bytes);
		spin_unlock(&sinfo->lock);

		if (count > 0)
			clear_extent_bit(io_tree, start, end, EXTENT_NORESERVE,
					 NULL);
	}

	return cow_file_range(inode, locked_page, start, end, page_started,
			      nr_written, 1, NULL);
}

struct can_nocow_file_extent_args {
	/* Input fields. */

	/* Start file offset of the range we want to NOCOW. */
	u64 start;
	/* End file offset (inclusive) of the range we want to NOCOW. */
	u64 end;
	bool writeback_path;
	bool strict;
	/*
	 * Free the path passed to can_nocow_file_extent() once it's not needed
	 * anymore.
	 */
	bool free_path;

	/* Output fields. Only set when can_nocow_file_extent() returns 1. */

	u64 disk_bytenr;
	u64 disk_num_bytes;
	u64 extent_offset;
	/* Number of bytes that can be written to in NOCOW mode. */
	u64 num_bytes;
};

/*
 * Check if we can NOCOW the file extent that the path points to.
 * This function may return with the path released, so the caller should check
 * if path->nodes[0] is NULL or not if it needs to use the path afterwards.
 *
 * Returns: < 0 on error
 *            0 if we can not NOCOW
 *            1 if we can NOCOW
 */
static int can_nocow_file_extent(struct btrfs_path *path,
				 struct btrfs_key *key,
				 struct btrfs_inode *inode,
				 struct can_nocow_file_extent_args *args)
{
	const bool is_freespace_inode = btrfs_is_free_space_inode(inode);
	struct extent_buffer *leaf = path->nodes[0];
	struct btrfs_root *root = inode->root;
	struct btrfs_file_extent_item *fi;
	u64 extent_end;
	u8 extent_type;
	int can_nocow = 0;
	int ret = 0;
	bool nowait = path->nowait;

	fi = btrfs_item_ptr(leaf, path->slots[0], struct btrfs_file_extent_item);
	extent_type = btrfs_file_extent_type(leaf, fi);

	if (extent_type == BTRFS_FILE_EXTENT_INLINE)
		goto out;

	/* Can't access these fields unless we know it's not an inline extent. */
	args->disk_bytenr = btrfs_file_extent_disk_bytenr(leaf, fi);
	args->disk_num_bytes = btrfs_file_extent_disk_num_bytes(leaf, fi);
	args->extent_offset = btrfs_file_extent_offset(leaf, fi);

	if (!(inode->flags & BTRFS_INODE_NODATACOW) &&
	    extent_type == BTRFS_FILE_EXTENT_REG)
		goto out;

	/*
	 * If the extent was created before the generation where the last snapshot
	 * for its subvolume was created, then this implies the extent is shared,
	 * hence we must COW.
	 */
	if (!args->strict &&
	    btrfs_file_extent_generation(leaf, fi) <=
	    btrfs_root_last_snapshot(&root->root_item))
		goto out;

	/* An explicit hole, must COW. */
	if (args->disk_bytenr == 0)
		goto out;

	/* Compressed/encrypted/encoded extents must be COWed. */
	if (btrfs_file_extent_compression(leaf, fi) ||
	    btrfs_file_extent_encryption(leaf, fi) ||
	    btrfs_file_extent_other_encoding(leaf, fi))
		goto out;

	extent_end = btrfs_file_extent_end(path);

	/*
	 * The following checks can be expensive, as they need to take other
	 * locks and do btree or rbtree searches, so release the path to avoid
	 * blocking other tasks for too long.
	 */
	btrfs_release_path(path);

	ret = btrfs_cross_ref_exist(root, btrfs_ino(inode),
				    key->offset - args->extent_offset,
				    args->disk_bytenr, false, path);
	WARN_ON_ONCE(ret > 0 && is_freespace_inode);
	if (ret != 0)
		goto out;

	if (args->free_path) {
		/*
		 * We don't need the path anymore, plus through the
		 * csum_exist_in_range() call below we will end up allocating
		 * another path. So free the path to avoid unnecessary extra
		 * memory usage.
		 */
		btrfs_free_path(path);
		path = NULL;
	}

	/* If there are pending snapshots for this root, we must COW. */
	if (args->writeback_path && !is_freespace_inode &&
	    atomic_read(&root->snapshot_force_cow))
		goto out;

	args->disk_bytenr += args->extent_offset;
	args->disk_bytenr += args->start - key->offset;
	args->num_bytes = min(args->end + 1, extent_end) - args->start;

	/*
	 * Force COW if csums exist in the range. This ensures that csums for a
	 * given extent are either valid or do not exist.
	 */
	ret = csum_exist_in_range(root->fs_info, args->disk_bytenr, args->num_bytes,
				  nowait);
	WARN_ON_ONCE(ret > 0 && is_freespace_inode);
	if (ret != 0)
		goto out;

	can_nocow = 1;
 out:
	if (args->free_path && path)
		btrfs_free_path(path);

	return ret < 0 ? ret : can_nocow;
}

/*
 * when nowcow writeback call back.  This checks for snapshots or COW copies
 * of the extents that exist in the file, and COWs the file as required.
 *
 * If no cow copies or snapshots exist, we write directly to the existing
 * blocks on disk
 */
static noinline int run_delalloc_nocow(struct btrfs_inode *inode,
				       struct page *locked_page,
				       const u64 start, const u64 end,
				       int *page_started,
				       unsigned long *nr_written)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	struct btrfs_root *root = inode->root;
	struct btrfs_path *path;
	u64 cow_start = (u64)-1;
	u64 cur_offset = start;
	int ret;
	bool check_prev = true;
	u64 ino = btrfs_ino(inode);
	struct btrfs_block_group *bg;
	bool nocow = false;
	struct can_nocow_file_extent_args nocow_args = { 0 };

	path = btrfs_alloc_path();
	if (!path) {
		extent_clear_unlock_delalloc(inode, start, end, locked_page,
					     EXTENT_LOCKED | EXTENT_DELALLOC |
					     EXTENT_DO_ACCOUNTING |
					     EXTENT_DEFRAG, PAGE_UNLOCK |
					     PAGE_START_WRITEBACK |
					     PAGE_END_WRITEBACK);
		return -ENOMEM;
	}

	nocow_args.end = end;
	nocow_args.writeback_path = true;

	while (1) {
		struct btrfs_key found_key;
		struct btrfs_file_extent_item *fi;
		struct extent_buffer *leaf;
		u64 extent_end;
		u64 ram_bytes;
		u64 nocow_end;
		int extent_type;

		nocow = false;

		ret = btrfs_lookup_file_extent(NULL, root, path, ino,
					       cur_offset, 0);
		if (ret < 0)
			goto error;

		/*
		 * If there is no extent for our range when doing the initial
		 * search, then go back to the previous slot as it will be the
		 * one containing the search offset
		 */
		if (ret > 0 && path->slots[0] > 0 && check_prev) {
			leaf = path->nodes[0];
			btrfs_item_key_to_cpu(leaf, &found_key,
					      path->slots[0] - 1);
			if (found_key.objectid == ino &&
			    found_key.type == BTRFS_EXTENT_DATA_KEY)
				path->slots[0]--;
		}
		check_prev = false;
next_slot:
		/* Go to next leaf if we have exhausted the current one */
		leaf = path->nodes[0];
		if (path->slots[0] >= btrfs_header_nritems(leaf)) {
			ret = btrfs_next_leaf(root, path);
			if (ret < 0) {
				if (cow_start != (u64)-1)
					cur_offset = cow_start;
				goto error;
			}
			if (ret > 0)
				break;
			leaf = path->nodes[0];
		}

		btrfs_item_key_to_cpu(leaf, &found_key, path->slots[0]);

		/* Didn't find anything for our INO */
		if (found_key.objectid > ino)
			break;
		/*
		 * Keep searching until we find an EXTENT_ITEM or there are no
		 * more extents for this inode
		 */
		if (WARN_ON_ONCE(found_key.objectid < ino) ||
		    found_key.type < BTRFS_EXTENT_DATA_KEY) {
			path->slots[0]++;
			goto next_slot;
		}

		/* Found key is not EXTENT_DATA_KEY or starts after req range */
		if (found_key.type > BTRFS_EXTENT_DATA_KEY ||
		    found_key.offset > end)
			break;

		/*
		 * If the found extent starts after requested offset, then
		 * adjust extent_end to be right before this extent begins
		 */
		if (found_key.offset > cur_offset) {
			extent_end = found_key.offset;
			extent_type = 0;
			goto out_check;
		}

		/*
		 * Found extent which begins before our range and potentially
		 * intersect it
		 */
		fi = btrfs_item_ptr(leaf, path->slots[0],
				    struct btrfs_file_extent_item);
		extent_type = btrfs_file_extent_type(leaf, fi);
		/* If this is triggered then we have a memory corruption. */
		ASSERT(extent_type < BTRFS_NR_FILE_EXTENT_TYPES);
		if (WARN_ON(extent_type >= BTRFS_NR_FILE_EXTENT_TYPES)) {
			ret = -EUCLEAN;
			goto error;
		}
		ram_bytes = btrfs_file_extent_ram_bytes(leaf, fi);
		extent_end = btrfs_file_extent_end(path);

		/*
		 * If the extent we got ends before our current offset, skip to
		 * the next extent.
		 */
		if (extent_end <= cur_offset) {
			path->slots[0]++;
			goto next_slot;
		}

		nocow_args.start = cur_offset;
		ret = can_nocow_file_extent(path, &found_key, inode, &nocow_args);
		if (ret < 0) {
			if (cow_start != (u64)-1)
				cur_offset = cow_start;
			goto error;
		} else if (ret == 0) {
			goto out_check;
		}

		ret = 0;
		bg = btrfs_inc_nocow_writers(fs_info, nocow_args.disk_bytenr);
		if (bg)
			nocow = true;
out_check:
		/*
		 * If nocow is false then record the beginning of the range
		 * that needs to be COWed
		 */
		if (!nocow) {
			if (cow_start == (u64)-1)
				cow_start = cur_offset;
			cur_offset = extent_end;
			if (cur_offset > end)
				break;
			if (!path->nodes[0])
				continue;
			path->slots[0]++;
			goto next_slot;
		}

		/*
		 * COW range from cow_start to found_key.offset - 1. As the key
		 * will contain the beginning of the first extent that can be
		 * NOCOW, following one which needs to be COW'ed
		 */
		if (cow_start != (u64)-1) {
			ret = fallback_to_cow(inode, locked_page,
					      cow_start, found_key.offset - 1,
					      page_started, nr_written);
			if (ret)
				goto error;
			cow_start = (u64)-1;
		}

		nocow_end = cur_offset + nocow_args.num_bytes - 1;

		if (extent_type == BTRFS_FILE_EXTENT_PREALLOC) {
			u64 orig_start = found_key.offset - nocow_args.extent_offset;
			struct extent_map *em;

			em = create_io_em(inode, cur_offset, nocow_args.num_bytes,
					  orig_start,
					  nocow_args.disk_bytenr, /* block_start */
					  nocow_args.num_bytes, /* block_len */
					  nocow_args.disk_num_bytes, /* orig_block_len */
					  ram_bytes, BTRFS_COMPRESS_NONE,
					  BTRFS_ORDERED_PREALLOC);
			if (IS_ERR(em)) {
				ret = PTR_ERR(em);
				goto error;
			}
			free_extent_map(em);
			ret = btrfs_add_ordered_extent(inode,
					cur_offset, nocow_args.num_bytes,
					nocow_args.num_bytes,
					nocow_args.disk_bytenr,
					nocow_args.num_bytes, 0,
					1 << BTRFS_ORDERED_PREALLOC,
					BTRFS_COMPRESS_NONE);
			if (ret) {
				btrfs_drop_extent_map_range(inode, cur_offset,
							    nocow_end, false);
				goto error;
			}
		} else {
			ret = btrfs_add_ordered_extent(inode, cur_offset,
						       nocow_args.num_bytes,
						       nocow_args.num_bytes,
						       nocow_args.disk_bytenr,
						       nocow_args.num_bytes,
						       0,
						       1 << BTRFS_ORDERED_NOCOW,
						       BTRFS_COMPRESS_NONE);
			if (ret)
				goto error;
		}

		if (nocow) {
			btrfs_dec_nocow_writers(bg);
			nocow = false;
		}

		if (btrfs_is_data_reloc_root(root))
			/*
			 * Error handled later, as we must prevent
			 * extent_clear_unlock_delalloc() in error handler
			 * from freeing metadata of created ordered extent.
			 */
			ret = btrfs_reloc_clone_csums(inode, cur_offset,
						      nocow_args.num_bytes);

		extent_clear_unlock_delalloc(inode, cur_offset, nocow_end,
					     locked_page, EXTENT_LOCKED |
					     EXTENT_DELALLOC |
					     EXTENT_CLEAR_DATA_RESV,
					     PAGE_UNLOCK | PAGE_SET_ORDERED);

		cur_offset = extent_end;

		/*
		 * btrfs_reloc_clone_csums() error, now we're OK to call error
		 * handler, as metadata for created ordered extent will only
		 * be freed by btrfs_finish_ordered_io().
		 */
		if (ret)
			goto error;
		if (cur_offset > end)
			break;
	}
	btrfs_release_path(path);

	if (cur_offset <= end && cow_start == (u64)-1)
		cow_start = cur_offset;

	if (cow_start != (u64)-1) {
		cur_offset = end;
		ret = fallback_to_cow(inode, locked_page, cow_start, end,
				      page_started, nr_written);
		if (ret)
			goto error;
	}

error:
	if (nocow)
		btrfs_dec_nocow_writers(bg);

	if (ret && cur_offset < end)
		extent_clear_unlock_delalloc(inode, cur_offset, end,
					     locked_page, EXTENT_LOCKED |
					     EXTENT_DELALLOC | EXTENT_DEFRAG |
					     EXTENT_DO_ACCOUNTING, PAGE_UNLOCK |
					     PAGE_START_WRITEBACK |
					     PAGE_END_WRITEBACK);
	btrfs_free_path(path);
	return ret;
}

static bool should_nocow(struct btrfs_inode *inode, u64 start, u64 end)
{
	if (inode->flags & (BTRFS_INODE_NODATACOW | BTRFS_INODE_PREALLOC)) {
		if (inode->defrag_bytes &&
		    test_range_bit(&inode->io_tree, start, end, EXTENT_DEFRAG,
				   0, NULL))
			return false;
		return true;
	}
	return false;
}

/*
 * Function to process delayed allocation (create CoW) for ranges which are
 * being touched for the first time.
 */
int btrfs_run_delalloc_range(struct btrfs_inode *inode, struct page *locked_page,
		u64 start, u64 end, int *page_started, unsigned long *nr_written,
		struct writeback_control *wbc)
{
	int ret;
	const bool zoned = btrfs_is_zoned(inode->root->fs_info);

	/*
	 * The range must cover part of the @locked_page, or the returned
	 * @page_started can confuse the caller.
	 */
	ASSERT(!(end <= page_offset(locked_page) ||
		 start >= page_offset(locked_page) + PAGE_SIZE));

	if (should_nocow(inode, start, end)) {
		/*
		 * Normally on a zoned device we're only doing COW writes, but
		 * in case of relocation on a zoned filesystem we have taken
		 * precaution, that we're only writing sequentially. It's safe
		 * to use run_delalloc_nocow() here, like for  regular
		 * preallocated inodes.
		 */
		ASSERT(!zoned || btrfs_is_data_reloc_root(inode->root));
		ret = run_delalloc_nocow(inode, locked_page, start, end,
					 page_started, nr_written);
	} else if (!btrfs_inode_can_compress(inode) ||
		   !inode_need_compress(inode, start, end)) {
		if (zoned)
			ret = run_delalloc_zoned(inode, locked_page, start, end,
						 page_started, nr_written);
		else
			ret = cow_file_range(inode, locked_page, start, end,
					     page_started, nr_written, 1, NULL);
	} else {
		set_bit(BTRFS_INODE_HAS_ASYNC_EXTENT, &inode->runtime_flags);
		ret = cow_file_range_async(inode, wbc, locked_page, start, end,
					   page_started, nr_written);
	}
	ASSERT(ret <= 0);
	if (ret)
		btrfs_cleanup_ordered_extents(inode, locked_page, start,
					      end - start + 1);
	return ret;
}

void btrfs_split_delalloc_extent(struct btrfs_inode *inode,
				 struct extent_state *orig, u64 split)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	u64 size;

	/* not delalloc, ignore it */
	if (!(orig->state & EXTENT_DELALLOC))
		return;

	size = orig->end - orig->start + 1;
	if (size > fs_info->max_extent_size) {
		u32 num_extents;
		u64 new_size;

		/*
		 * See the explanation in btrfs_merge_delalloc_extent, the same
		 * applies here, just in reverse.
		 */
		new_size = orig->end - split + 1;
		num_extents = count_max_extents(fs_info, new_size);
		new_size = split - orig->start;
		num_extents += count_max_extents(fs_info, new_size);
		if (count_max_extents(fs_info, size) >= num_extents)
			return;
	}

	spin_lock(&inode->lock);
	btrfs_mod_outstanding_extents(inode, 1);
	spin_unlock(&inode->lock);
}

/*
 * Handle merged delayed allocation extents so we can keep track of new extents
 * that are just merged onto old extents, such as when we are doing sequential
 * writes, so we can properly account for the metadata space we'll need.
 */
void btrfs_merge_delalloc_extent(struct btrfs_inode *inode, struct extent_state *new,
				 struct extent_state *other)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	u64 new_size, old_size;
	u32 num_extents;

	/* not delalloc, ignore it */
	if (!(other->state & EXTENT_DELALLOC))
		return;

	if (new->start > other->start)
		new_size = new->end - other->start + 1;
	else
		new_size = other->end - new->start + 1;

	/* we're not bigger than the max, unreserve the space and go */
	if (new_size <= fs_info->max_extent_size) {
		spin_lock(&inode->lock);
		btrfs_mod_outstanding_extents(inode, -1);
		spin_unlock(&inode->lock);
		return;
	}

	/*
	 * We have to add up either side to figure out how many extents were
	 * accounted for before we merged into one big extent.  If the number of
	 * extents we accounted for is <= the amount we need for the new range
	 * then we can return, otherwise drop.  Think of it like this
	 *
	 * [ 4k][MAX_SIZE]
	 *
	 * So we've grown the extent by a MAX_SIZE extent, this would mean we
	 * need 2 outstanding extents, on one side we have 1 and the other side
	 * we have 1 so they are == and we can return.  But in this case
	 *
	 * [MAX_SIZE+4k][MAX_SIZE+4k]
	 *
	 * Each range on their own accounts for 2 extents, but merged together
	 * they are only 3 extents worth of accounting, so we need to drop in
	 * this case.
	 */
	old_size = other->end - other->start + 1;
	num_extents = count_max_extents(fs_info, old_size);
	old_size = new->end - new->start + 1;
	num_extents += count_max_extents(fs_info, old_size);
	if (count_max_extents(fs_info, new_size) >= num_extents)
		return;

	spin_lock(&inode->lock);
	btrfs_mod_outstanding_extents(inode, -1);
	spin_unlock(&inode->lock);
}

static void btrfs_add_delalloc_inodes(struct btrfs_root *root,
				      struct btrfs_inode *inode)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;

	spin_lock(&root->delalloc_lock);
	if (list_empty(&inode->delalloc_inodes)) {
		list_add_tail(&inode->delalloc_inodes, &root->delalloc_inodes);
		set_bit(BTRFS_INODE_IN_DELALLOC_LIST, &inode->runtime_flags);
		root->nr_delalloc_inodes++;
		if (root->nr_delalloc_inodes == 1) {
			spin_lock(&fs_info->delalloc_root_lock);
			BUG_ON(!list_empty(&root->delalloc_root));
			list_add_tail(&root->delalloc_root,
				      &fs_info->delalloc_roots);
			spin_unlock(&fs_info->delalloc_root_lock);
		}
	}
	spin_unlock(&root->delalloc_lock);
}

void __btrfs_del_delalloc_inode(struct btrfs_root *root,
				struct btrfs_inode *inode)
{
	struct btrfs_fs_info *fs_info = root->fs_info;

	if (!list_empty(&inode->delalloc_inodes)) {
		list_del_init(&inode->delalloc_inodes);
		clear_bit(BTRFS_INODE_IN_DELALLOC_LIST,
			  &inode->runtime_flags);
		root->nr_delalloc_inodes--;
		if (!root->nr_delalloc_inodes) {
			ASSERT(list_empty(&root->delalloc_inodes));
			spin_lock(&fs_info->delalloc_root_lock);
			BUG_ON(list_empty(&root->delalloc_root));
			list_del_init(&root->delalloc_root);
			spin_unlock(&fs_info->delalloc_root_lock);
		}
	}
}

static void btrfs_del_delalloc_inode(struct btrfs_root *root,
				     struct btrfs_inode *inode)
{
	spin_lock(&root->delalloc_lock);
	__btrfs_del_delalloc_inode(root, inode);
	spin_unlock(&root->delalloc_lock);
}

/*
 * Properly track delayed allocation bytes in the inode and to maintain the
 * list of inodes that have pending delalloc work to be done.
 */
void btrfs_set_delalloc_extent(struct btrfs_inode *inode, struct extent_state *state,
			       u32 bits)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;

	if ((bits & EXTENT_DEFRAG) && !(bits & EXTENT_DELALLOC))
		WARN_ON(1);
	/*
	 * set_bit and clear bit hooks normally require _irqsave/restore
	 * but in this case, we are only testing for the DELALLOC
	 * bit, which is only set or cleared with irqs on
	 */
	if (!(state->state & EXTENT_DELALLOC) && (bits & EXTENT_DELALLOC)) {
		struct btrfs_root *root = inode->root;
		u64 len = state->end + 1 - state->start;
		u32 num_extents = count_max_extents(fs_info, len);
		bool do_list = !btrfs_is_free_space_inode(inode);

		spin_lock(&inode->lock);
		btrfs_mod_outstanding_extents(inode, num_extents);
		spin_unlock(&inode->lock);

		/* For sanity tests */
		if (btrfs_is_testing(fs_info))
			return;

		percpu_counter_add_batch(&fs_info->delalloc_bytes, len,
					 fs_info->delalloc_batch);
		spin_lock(&inode->lock);
		inode->delalloc_bytes += len;
		if (bits & EXTENT_DEFRAG)
			inode->defrag_bytes += len;
		if (do_list && !test_bit(BTRFS_INODE_IN_DELALLOC_LIST,
					 &inode->runtime_flags))
			btrfs_add_delalloc_inodes(root, inode);
		spin_unlock(&inode->lock);
	}

	if (!(state->state & EXTENT_DELALLOC_NEW) &&
	    (bits & EXTENT_DELALLOC_NEW)) {
		spin_lock(&inode->lock);
		inode->new_delalloc_bytes += state->end + 1 - state->start;
		spin_unlock(&inode->lock);
	}
}

/*
 * Once a range is no longer delalloc this function ensures that proper
 * accounting happens.
 */
void btrfs_clear_delalloc_extent(struct btrfs_inode *inode,
				 struct extent_state *state, u32 bits)
{
	struct btrfs_fs_info *fs_info = inode->root->fs_info;
	u64 len = state->end + 1 - state->start;
	u32 num_extents = count_max_extents(fs_info, len);

	if ((state->state & EXTENT_DEFRAG) && (bits & EXTENT_DEFRAG)) {
		spin_lock(&inode->lock);
		inode->defrag_bytes -= len;
		spin_unlock(&inode->lock);
	}

	/*
	 * set_bit and clear bit hooks normally require _irqsave/restore
	 * but in this case, we are only testing for the DELALLOC
	 * bit, which is only set or cleared with irqs on
	 */
	if ((state->state & EXTENT_DELALLOC) && (bits & EXTENT_DELALLOC)) {
		struct btrfs_root *root = inode->root;
		bool do_list = !btrfs_is_free_space_inode(inode);

		spin_lock(&inode->lock);
		btrfs_mod_outstanding_extents(inode, -num_extents);
		spin_unlock(&inode->lock);

		/*
		 * We don't reserve metadata space for space cache inodes so we
		 * don't need to call delalloc_release_metadata if there is an
		 * error.
		 */
		if (bits & EXTENT_CLEAR_META_RESV &&
		    root != fs_info->tree_root)
			btrfs_delalloc_release_metadata(inode, len, false);

		/* For sanity tests. */
		if (btrfs_is_testing(fs_info))
			return;

		if (!btrfs_is_data_reloc_root(root) &&
		    do_list && !(state->state & EXTENT_NORESERVE) &&
		    (bits & EXTENT_CLEAR_DATA_RESV))
			btrfs_free_reserved_data_space_noquota(fs_info, len);

		percpu_counter_add_batch(&fs_info->delalloc_bytes, -len,
					 fs_info->delalloc_batch);
		spin_lock(&inode->lock);
		inode->delalloc_bytes -= len;
		if (do_list && inode->delalloc_bytes == 0 &&
		    test_bit(BTRFS_INODE_IN_DELALLOC_LIST,
					&inode->runtime_flags))
			btrfs_del_delalloc_inode(root, inode);
		spin_unlock(&inode->lock);
	}

	if ((state->state & EXTENT_DELALLOC_NEW) &&
	    (bits & EXTENT_DELALLOC_NEW)) {
		spin_lock(&inode->lock);
		ASSERT(inode->new_delalloc_bytes >= len);
		inode->new_delalloc_bytes -= len;
		if (bits & EXTENT_ADD_INODE_BYTES)
			inode_add_bytes(&inode->vfs_inode, len);
		spin_unlock(&inode->lock);
	}
}

/*
 * Split an extent_map at [start, start + len]
 *
 * This function is intended to be used only for extract_ordered_extent().
 */
static int split_zoned_em(struct btrfs_inode *inode, u64 start, u64 len,
			  u64 pre, u64 post)
{
	struct extent_map_tree *em_tree = &inode->extent_tree;
	struct extent_map *em;
	struct extent_map *split_pre = NULL;
	struct extent_map *split_mid = NULL;
	struct extent_map *split_post = NULL;
	int ret = 0;
	unsigned long flags;

	/* Sanity check */
	if (pre == 0 && post == 0)
		return 0;

	split_pre = alloc_extent_map();
	if (pre)
		split_mid = alloc_extent_map();
	if (post)
		split_post = alloc_extent_map();
	if (!split_pre || (pre && !split_mid) || (post && !split_post)) {
		ret = -ENOMEM;
		goto out;
	}

	ASSERT(pre + post < len);

	lock_extent(&inode->io_tree, start, start + len - 1, NULL);
	write_lock(&em_tree->lock);
	em = lookup_extent_mapping(em_tree, start, len);
	if (!em) {
		ret = -EIO;
		goto out_unlock;
	}

	ASSERT(em->len == len);
	ASSERT(!test_bit(EXTENT_FLAG_COMPRESSED, &em->flags));
	ASSERT(em->block_start < EXTENT_MAP_LAST_BYTE);
	ASSERT(test_bit(EXTENT_FLAG_PINNED, &em->flags));
	ASSERT(!test_bit(EXTENT_FLAG_LOGGING, &em->flags));
	ASSERT(!list_empty(&em->list));

	flags = em->flags;
	clear_bit(EXTENT_FLAG_PINNED, &em->flags);

	/* First, replace the em with a new extent_map starting from * em->start */
	split_pre->start = em->start;
	split_pre->len = (pre ? pre : em->len - post);
	split_pre->orig_start = split_pre->start;
	split_pre->block_start = em->block_start;
	split_pre->block_len = split_pre->len;
	split_pre->orig_block_len = split_pre->block_len;
	split_pre->ram_bytes = split_pre->len;
	split_pre->flags = flags;
	split_pre->compress_type = em->compress_type;
	split_pre->generation = em->generation;

	replace_extent_mapping(em_tree, em, split_pre, 1);

	/*
	 * Now we only have an extent_map at:
	 *     [em->start, em->start + pre] if pre != 0
	 *     [em->start, em->start + em->len - post] if pre == 0
	 */

	if (pre) {
		/* Insert the middle extent_map */
		split_mid->start = em->start + pre;
		split_mid->len = em->len - pre - post;
		split_mid->orig_start = split_mid->start;
		split_mid->block_start = em->block_start + pre;
		split_mid->block_len = split_mid->len;
		split_mid->orig_block_len = split_mid->block_len;
		split_mid->ram_bytes = split_mid->len;
		split_mid->flags = flags;
		split_mid->compress_type = em->compress_type;
		split_mid->generation = em->generation;
		add_extent_mapping(em_tree, split_mid, 1);
	}

	if (post) {
		split_post->start = em->start + em->len - post;
		split_post->len = post;
		split_post->orig_start = split_post->start;
		split_post->block_start = em->block_start + em->len - post;
		split_post->block_len = split_post->len;
		split_post->orig_block_len = split_post->block_len;
		split_post->ram_bytes = split_post->len;
		split_post->flags = flags;
		split_post->compress_type = em->compress_type;
		split_post->generation = em->generation;
		add_extent_mapping(em_tree, split_post, 1);
	}

	/* Once for us */
	free_extent_map(em);
	/* Once for the tree */
	free_extent_map(em);

out_unlock:
	write_unlock(&em_tree->lock);
	unlock_extent(&inode->io_tree, start, start + len - 1, NULL);
out:
	free_extent_map(split_pre);
	free_extent_map(split_mid);
	free_extent_map(split_post);

	return ret;
}

blk_status_t btrfs_extract_ordered_extent(struct btrfs_bio *bbio)
{
	u64 start = (u64)bbio->bio.bi_iter.bi_sector << SECTOR_SHIFT;
	u64 len = bbio->bio.bi_iter.bi_size;
	struct btrfs_inode *inode = bbio->inode;
	struct btrfs_ordered_extent *ordered;
	u64 file_len;
	u64 end = start + len;
	u64 ordered_end;
	u64 pre, post;
	int ret = 0;

	ordered = btrfs_lookup_ordered_extent(inode, bbio->file_offset);
	if (WARN_ON_ONCE(!ordered))
		return BLK_STS_IOERR;

	/* No need to split */
	if (ordered->disk_num_bytes == len)
		goto out;

	/* We cannot split once end_bio'd ordered extent */
	if (WARN_ON_ONCE(ordered->bytes_left != ordered->disk_num_bytes)) {
		ret = -EINVAL;
		goto out;
	}

	/* We cannot split a compressed ordered extent */
	if (WARN_ON_ONCE(ordered->disk_num_bytes != ordered->num_bytes)) {
		ret = -EINVAL;
		goto out;
	}

	ordered_end = ordered->disk_bytenr + ordered->disk_num_bytes;
	/* bio must be in one ordered extent */
	if (WARN_ON_ONCE(start < ordered->disk_bytenr || end > ordered_end)) {
		ret = -EINVAL;
		goto out;
	}

	/* Checksum list should be empty */
	if (WARN_ON_ONCE(!list_empty(&ordered->list))) {
		ret = -EINVAL;
		goto out;
	}

	file_len = ordered->num_bytes;
	pre = start - ordered->disk_bytenr;
	post = ordered_end - end;

	ret = btrfs_split_ordered_extent(ordered, pre, post);
	if (ret)
		goto out;
	ret = split_zoned_em(inode, bbio->file_offset, file_len, pre, post);

out:
	btrfs_put_ordered_extent(ordered);

	return errno_to_blk_status(ret);
}

/*
 * given a list of ordered sums record them in the inode.  This happens
 * at IO completion time based on sums calculated at bio submission time.
 */
static int add_pending_csums(struct btrfs_trans_handle *trans,
			     struct list_head *list)
{
	struct btrfs_ordered_sum *sum;
	struct btrfs_root *csum_root = NULL;
	int ret;

	list_for_each_entry(sum, list, list) {
		trans->adding_csums = true;
		if (!csum_root)
			csum_root = btrfs_csum_root(trans->fs_info,
						    sum->bytenr);
		ret = btrfs_csum_file_blocks(trans, csum_root, sum);
		trans->adding_csums = false;
		if (ret)
			return ret;
	}
	return 0;
}

static int btrfs_find_new_delalloc_bytes(struct btrfs_inode *inode,
					 const u64 start,
					 const u64 len,
					 struct extent_state **cached_state)
{
	u64 search_start = start;
	const u64 end = start + len - 1;

	while (search_start < end) {
		const u64 search_len = end - search_start + 1;
		struct extent_map *em;
		u64 em_len;
		int ret = 0;

		em = btrfs_get_extent(inode, NULL, 0, search_start, search_len);
		if (IS_ERR(em))
			return PTR_ERR(em);

		if (em->block_start != EXTENT_MAP_HOLE)
			goto next;

		em_len = em->len;
		if (em->start < search_start)
			em_len -= search_start - em->start;
		if (em_len > search_len)
			em_len = search_len;

		ret = set_extent_bit(&inode->io_tree, search_start,
				     search_start + em_len - 1,
				     EXTENT_DELALLOC_NEW, cached_state,
				     GFP_NOFS);
next:
		search_start = extent_map_end(em);
		free_extent_map(em);
		if (ret)
			return ret;
	}
	return 0;
}

int btrfs_set_extent_delalloc(struct btrfs_inode *inode, u64 start, u64 end,
			      unsigned int extra_bits,
			      struct extent_state **cached_state)
{
	WARN_ON(PAGE_ALIGNED(end));

	if (start >= i_size_read(&inode->vfs_inode) &&
	    !(inode->flags & BTRFS_INODE_PREALLOC)) {
		/*
		 * There can't be any extents following eof in this case so just
		 * set the delalloc new bit for the range directly.
		 */
		extra_bits |= EXTENT_DELALLOC_NEW;
	} else {
		int ret;

		ret = btrfs_find_new_delalloc_bytes(inode, start,
						    end + 1 - start,
						    cached_state);
		if (ret)
			return ret;
	}

	return set_extent_delalloc(&inode->io_tree, start, end, extra_bits,
				   cached_state);
}

/* see btrfs_writepage_start_hook for details on why this is required */
struct btrfs_writepage_fixup {
	struct page *page;
	struct btrfs_inode *inode;
	struct btrfs_work work;
};

static void btrfs_writepage_fixup_worker(struct btrfs_work *work)
{
	struct btrfs_writepage_fixup *fixup;
	struct btrfs_ordered_extent *ordered;
	struct extent_state *cached_state = NULL;
	struct extent_changeset *data_reserved = NULL;
	struct page *page;
	struct btrfs_inode *inode;
	u64 page_start;
	u64 page_end;
	int ret = 0;
	bool free_delalloc_space = true;

	fixup = container_of(work, struct btrfs_writepage_fixup, work);
	page = fixup->page;
	inode = fixup->inode;
	page_start = page_offset(page);
	page_end = page_offset(page) + PAGE_SIZE - 1;

	/*
	 * This is similar to page_mkwrite, we need to reserve the space before
	 * we take the page lock.
	 */
	ret = btrfs_delalloc_reserve_space(inode, &data_reserved, page_start,
					   PAGE_SIZE);
again:
	lock_page(page);

	/*
	 * Before we queued this fixup, we took a reference on the page.
	 * page->mapping may go NULL, but it shouldn't be moved to a different
	 * address space.
	 */
	if (!page->mapping || !PageDirty(page) || !PageChecked(page)) {
		/*
		 * Unfortunately this is a little tricky, either
		 *
		 * 1) We got here and our page had already been dealt with and
		 *    we reserved our space, thus ret == 0, so we need to just
		 *    drop our space reservation and bail.  This can happen the
		 *    first time we come into the fixup worker, or could happen
		 *    while waiting for the ordered extent.
		 * 2) Our page was already dealt with, but we happened to get an
		 *    ENOSPC above from the btrfs_delalloc_reserve_space.  In
		 *    this case we obviously don't have anything to release, but
		 *    because the page was already dealt with we don't want to
		 *    mark the page with an error, so make sure we're resetting
		 *    ret to 0.  This is why we have this check _before_ the ret
		 *    check, because we do not want to have a surprise ENOSPC
		 *    when the page was already properly dealt with.
		 */
		if (!ret) {
			btrfs_delalloc_release_extents(inode, PAGE_SIZE);
			btrfs_delalloc_release_space(inode, data_reserved,
						     page_start, PAGE_SIZE,
						     true);
		}
		ret = 0;
		goto out_page;
	}

	/*
	 * We can't mess with the page state unless it is locked, so now that
	 * it is locked bail if we failed to make our space reservation.
	 */
	if (ret)
		goto out_page;

	lock_extent(&inode->io_tree, page_start, page_end, &cached_state);

	/* already ordered? We're done */
	if (PageOrdered(page))
		goto out_reserved;

	ordered = btrfs_lookup_ordered_range(inode, page_start, PAGE_SIZE);
	if (ordered) {
		unlock_extent(&inode->io_tree, page_start, page_end,
			      &cached_state);
		unlock_page(page);
		btrfs_start_ordered_extent(ordered);
		btrfs_put_ordered_extent(ordered);
		goto again;
	}

	ret = btrfs_set_extent_delalloc(inode, page_start, page_end, 0,
					&cached_state);
	if (ret)
		goto out_reserved;

	/*
	 * Everything went as planned, we're now the owner of a dirty page with
	 * delayed allocation bits set and space reserved for our COW
	 * destination.
	 *
	 * The page was dirty when we started, nothing should have cleaned it.
	 */
	BUG_ON(!PageDirty(page));
	free_delalloc_space = false;
out_reserved:
	btrfs_delalloc_release_extents(inode, PAGE_SIZE);
	if (free_delalloc_space)
		btrfs_delalloc_release_space(inode, data_reserved, page_start,
					     PAGE_SIZE, true);
	unlock_extent(&inode->io_tree, page_start, page_end, &cached_state);
out_page:
	if (ret) {
		/*
		 * We hit ENOSPC or other errors.  Update the mapping and page
		 * to reflect the errors and clean the page.
		 */
		mapping_set_error(page->mapping, ret);
		end_extent_writepage(page, ret, page_start, page_end);
		clear_page_dirty_for_io(page);
		SetPageError(page);
	}
	btrfs_page_clear_checked(inode->root->fs_info, page, page_start, PAGE_SIZE);
	unlock_page(page);
	put_page(page);
	kfree(fixup);
	extent_changeset_free(data_reserved);
	/*
	 * As a precaution, do a delayed iput in case it would be the last iput
	 * that could need flushing space. Recursing back to fixup worker would
	 * deadlock.
	 */
	btrfs_add_delayed_iput(inode);
}

/*
 * There are a few paths in the higher layers of the kernel that directly
 * set the page dirty bit without asking the filesystem if it is a
 * good idea.  This causes problems because we want to make sure COW
 * properly happens and the data=ordered rules are followed.
 *
 * In our case any range that doesn't have the ORDERED bit set
 * hasn't been properly setup for IO.  We kick off an async process
 * to fix it up.  The async helper will wait for ordered extents, set
 * the delalloc bit and make it safe to write the page.
 */
int btrfs_writepage_cow_fixup(struct page *page)
{
	struct inode *inode = page->mapping->host;
	struct btrfs_fs_info *fs_info = btrfs_sb(inode->i_sb);
	struct btrfs_writepage_fixup *fixup;

	/* This page has ordered extent covering it already */
	if (PageOrdered(page))
		return 0;

	/*
	 * PageChecked is set below when we create a fixup worker for this page,
	 * don't try to create another one if we're already PageChecked()
	 *
	 * The extent_io writepage code will redirty the page if we send back
	 * EAGAIN.
	 */
	if (PageChecked(page))
		return -EAGAIN;

	fixup = kzalloc(sizeof(*fixup), GFP_NOFS);
	if (!fixup)
		return -EAGAIN;

	/*
	 * We are already holding a reference to this inode from
	 * write_cache_pages.  We need to hold it because the space reservation
	 * takes place outside of the page lock, and we can't trust
	 * page->mapping outside of the page lock.
	 */
	ihold(inode);
	btrfs_page_set_checked(fs_info, page, page_offset(page), PAGE_SIZE);
	get_page(page);
	btrfs_init_work(&fixup->work, btrfs_writepage_fixup_worker, NULL, NULL);
	fixup->page = page;
	fixup->inode = BTRFS_I(inode);
	btrfs_queue_work(fs_info->fixup_workers, &fixup->work);

	return -EAGAIN;
}

static int insert_reserved_file_extent(struct btrfs_trans_handle *trans,
				       struct btrfs_inode *inode, u64 file_pos,
				       struct btrfs_file_extent_item *stack_fi,
				       const bool update_inode_bytes,
				       u64 qgroup_reserved)
{
	struct btrfs_root *root = inode->root;
	const u64 sectorsize = root->fs_info->sectorsize;
	struct btrfs_path *path;
	struct extent_buffer *leaf;
	struct btrfs_key ins;
	u64 disk_num_bytes = btrfs_stack_file_extent_disk_num_bytes(stack_fi);
	u64 disk_bytenr = btrfs_stack_file_extent_disk_bytenr(stack_fi);
	u64 offset = btrfs_stack_file_extent_offset(stack_fi);
	u64 num_bytes = btrfs_stack_file_extent_num_bytes(stack_fi);
	u64 ram_bytes = btrfs_stack_file_extent_ram_bytes(stack_fi);
	struct btrfs_drop_extents_args drop_args = { 0 };
	int ret;

	path = btrfs_alloc_path();
	if (!path)
		return -ENOMEM;

	/*
	 * we may be replacing one extent in the tree with another.
	 * The new extent is pinned in the extent map, and we don't want
	 * to drop it from the cache until it is completely in the btree.
	 *
	 * So, tell btrfs_drop_extents to leave this extent in the cache.
	 * the caller is expected to unpin it and allow it to be merged
	 * with the others.
	 */
	drop_args.path = path;
	drop_args.start = file_pos;
	drop_args.end = file_pos + num_bytes;
	drop_args.replace_extent = true;
	drop_args.extent_item_size = sizeof(*stack_fi);
	ret = btrfs_drop_extents(trans, root, inode, &drop_args);
	if (ret)
		goto out;

	if (!drop_args.extent_inserted) {
		ins.objectid = btrfs_ino(inode);
		ins.offset = file_pos;
		ins.type = BTRFS_EXTENT_DATA_KEY;

		ret = btrfs_insert_empty_item(trans, root, path, &ins,
					      sizeof(*stack_fi));
		if (ret)
			goto out;
	}
	leaf = path->nodes[0];
	btrfs_set_stack_file_extent_generation(stack_fi, trans->transid);
	write_extent_buffer(leaf, stack_fi,
			btrfs_item_ptr_offset(leaf, path->slots[0]),
			sizeof(struct btrfs_file_extent_item));

	btrfs_mark_buffer_dirty(leaf);
	btrfs_release_path(path);

	/*
	 * If we dropped an inline extent here, we know the range where it is
	 * was not marked with the EXTENT_DELALLOC_NEW bit, so we update the
	 * number of bytes only for that range containing the inline extent.
	 * The remaining of the range will be processed when clearning the
	 * EXTENT_DELALLOC_BIT bit through the ordered extent completion.
	 */
	if (file_pos == 0 && !IS_ALIGNED(drop_args.bytes_found, sectorsize)) {
		u64 inline_size = round_down(drop_args.bytes_found, sectorsize);

		inline_size = drop_args.bytes_found - inline_size;
		btrfs_update_inode_bytes(inode, sectorsize, inline_size);
		drop_args.bytes_found -= inline_size;
		num_bytes -= sectorsize;
	}

	if (update_inode_bytes)
		btrfs_update_inode_bytes(inode, num_bytes, drop_args.bytes_found);

	ins.objectid = disk_bytenr;
	ins.offset = disk_num_bytes;
	ins.type = BTRFS_EXTENT_ITEM_KEY;

	ret = btrfs_inode_set_file_extent_range(inode, file_pos, ram_bytes);
	if (ret)
		goto out;

	ret = btrfs_alloc_reserved_file_extent(trans, root, btrfs_ino(inode),
					       file_pos - offset,
					       qgroup_reserved, &ins);
out:
	btrfs_free_path(path);

	return ret;
}

static void btrfs_release_delalloc_bytes(struct btrfs_fs_info *fs_info,
					 u64 start, u64 len)
{
	struct btrfs_block_group *cache;

	cache = btrfs_lookup_block_group(fs_info, start);
	ASSERT(cache);

	spin_lock(&cache->lock);
	cache->delalloc_bytes -= len;
	spin_unlock(&cache->lock);

	btrfs_put_block_group(cache);
}

static int insert_ordered_extent_file_extent(struct btrfs_trans_handle *trans,
					     struct btrfs_ordered_extent *oe)
{
	struct btrfs_file_extent_item stack_fi;
	bool update_inode_bytes;
	u64 num_bytes = oe->num_bytes;
	u64 ram_bytes = oe->ram_bytes;

	memset(&stack_fi, 0, sizeof(stack_fi));
	btrfs_set_stack_file_extent_type(&stack_fi, BTRFS_FILE_EXTENT_REG);
	btrfs_set_stack_file_extent_disk_bytenr(&stack_fi, oe->disk_bytenr);
	btrfs_set_stack_file_extent_disk_num_bytes(&stack_fi,
						   oe->disk_num_bytes);
	btrfs_set_stack_file_extent_offset(&stack_fi, oe->offset);
	if (test_bit(BTRFS_ORDERED_TRUNCATED, &oe->flags)) {
		num_bytes = oe->truncated_len;
		ram_bytes = num_bytes;
	}
	btrfs_set_stack_file_extent_num_bytes(&stack_fi, num_bytes);
	btrfs_set_stack_file_extent_ram_bytes(&stack_fi, ram_bytes);
	btrfs_set_stack_file_extent_compression(&stack_fi, oe->compress_type);
	/* Encryption and other encoding is reserved and all 0 */

	/*
	 * For delalloc, when completing an ordered extent we update the inode's
	 * bytes when clearing the range in the inode's io tree, so pass false
	 * as the argument 'update_inode_bytes' to insert_reserved_file_extent(),
	 * except if the ordered extent was truncated.
	 */
	update_inode_bytes = test_bit(BTRFS_ORDERED_DIRECT, &oe->flags) ||
			     test_bit(BTRFS_ORDERED_ENCODED, &oe->flags) ||
			     test_bit(BTRFS_ORDERED_TRUNCATED, &oe->flags);

	return insert_reserved_file_extent(trans, BTRFS_I(oe->inode),
					   oe->file_offset, &stack_fi,
					   update_inode_bytes, oe->qgroup_rsv);
}

/*
 * As ordered data IO finishes, this gets called so we can finish
 * an ordered extent if the range of bytes in the file it covers are
 * fully written.
 */
int btrfs_finish_ordered_io(struct btrfs_ordered_extent *ordered_extent)
{
	struct btrfs_inode *inode = BTRFS_I(ordered_extent->inode);
	struct btrfs_root *root = inode->root;
	struct btrfs_fs_info *fs_info = root->fs_info;
	struct btrfs_trans_handle *trans = NULL;
	struct extent_io_tree *io_tree = &inode->io_tree;
	struct extent_state *cached_state = NULL;
	u64 start, end;
	int compress_type = 0;
	int ret = 0;
	u64 logical_len = ordered_extent->num_bytes;
	bool freespace_inode;
	bool truncated = false;
	bool clear_reserved_extent = true;
	unsigned int clear_bits = EXTENT_DEFRAG;

	start = ordered_extent->file_offset;
	end = start + ordered_extent->num_bytes - 1;

	if (!test_bit(BTRFS_ORDERED_NOCOW, &ordered_extent->flags) &&
	    !test_bit(BTRFS_ORDERED_PREALLOC, &ordered_extent->flags) &&
	    !test_bit(BTRFS_ORDERED_DIRECT, &ordered_extent->flags) &&
	    !test_bit(BTRFS_ORDERED_ENCODED, &ordered_extent->flags))
		clear_bits |= EXTENT_DELALLOC_NEW;

	freespace_inode = btrfs_is_free_space_inode(inode);
	if (!freespace_inode)
		btrfs_lockdep_acquire(fs_info, btrfs_ordered_extent);

	if (test_bit(BTRFS_ORDERED_IOERR, &ordered_extent->flags)) {
		ret = -EIO;
		goto out;
	}

	/* A valid ->physical implies a write on a sequential zone. */
	if (ordered_extent->physical != (u64)-1) {
		btrfs_rewrite_logical_zoned(ordered_extent);
		btrfs_zone_finish_endio(fs_info, ordered_extent->disk_bytenr,
					ordered_extent->disk_num_bytes);
	}

	if (test_bit(BTRFS_ORDERED_TRUNCATED, &ordered_extent->flags)) {
		truncated = true;
		logical_len = ordered_extent->truncated_len;
		/* Truncated the entire extent, don't bother adding */
		if (!logical_len)
			goto out;
	}

	if (test_bit(BTRFS_ORDERED_NOCOW, &ordered_extent->flags)) {
		BUG_ON(!list_empty(&ordered_extent->list)); /* Logic error */

		btrfs_inode_safe_disk_i_size_write(inode, 0);
		if (freespace_inode)
			trans = btrfs_join_transaction_spacecache(root);
		else
			trans = btrfs_join_transaction(root);
		if (IS_ERR(trans)) {
			ret = PTR_ERR(trans);
			trans = NULL;
			goto out;
		}
		trans->block_rsv = &inode->block_rsv;
		ret = btrfs_update_inode_fallback(trans, root, inode);
		if (ret) /* -ENOMEM or corruption */
			btrfs_abort_transaction(trans, ret);
		goto out;
	}

	clear_bits |= EXTENT_LOCKED;
	lock_extent(io_tree, start, end, &cached_state);

	if (freespace_inode)
		trans = btrfs_join_transaction_spacecache(root);
	else
		trans = btrfs_join_transaction(root);
	if (IS_ERR(trans)) {
		ret = PTR_ERR(trans);
		trans = NULL;
		goto out;
	}

	trans->block_rsv = &inode->block_rsv;

	if (test_bit(BTRFS_ORDERED_COMPRESSED, &ordered_extent->flags))
		compress_type = ordered_extent->compress_type;
	if (test_bit(BTRFS_ORDERED_PREALLOC, &ordered_extent->flags)) {
		BUG_ON(compress_type);
		ret = btrfs_mark_extent_written(trans, inode,
						ordered_extent->file_offset,
						ordered_extent->file_offset +
						logical_len);
		btrfs_zoned_release_data_reloc_bg(fs_info, ordered_extent->disk_bytenr,
						  ordered_extent->disk_num_bytes);
	} else {
		BUG_ON(root == fs_info->tree_root);
		ret = insert_ordered_extent_file_extent(trans, ordered_extent);
		if (!ret) {
			clear_reserved_extent = false;
			btrfs_release_delalloc_bytes(fs_info,
						ordered_extent->disk_bytenr,
						ordered_extent->disk_num_bytes);
		}
	}
	unpin_extent_cache(&inode->extent_tree, ordered_extent->file_offset,
			   ordered_extent->num_bytes, trans->transid);
	if (ret < 0) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	}

	ret = add_pending_csums(trans, &ordered_extent->list);
	if (ret) {
		btrfs_abort_transaction(trans, ret);
		goto out;
	}

	/*
	 * If this is a new delalloc range, clear its new delalloc flag to
	 * update the inode's number of bytes. This needs to be done first
	 * before updating the inode item.
	 */
	if ((clear_bits & EXTENT_DELALLOC_NEW) &&
	    !test_bit(BTRFS_ORDERED_TRUNCATED, &ordered_extent->flags))
		clear_extent_bit(&inode->io_tree, start, end,
				 EXTENT_DELALLOC_NEW | EXTENT_ADD_INODE_BYTES,
				 &cached_state);

	btrfs_inode_safe_disk_i_size_write(inode, 0);
	ret = btrfs_update_inode_fallback(trans, root, inode);
	if (ret) { /* -ENOMEM or corruption */
		btrfs_abort_transaction(trans, ret);
		goto out;
	}
	ret = 0;
out:
	clear_extent_bit(&inode->io_tree, start, end, clear_bits,
			 &cached_state);

	if (trans)
		btrfs_end_transaction(trans);

	if (ret || truncated) {
		u64 unwritten_start = start;

		/*
		 * If we failed to finish this ordered extent for any reason we
		 * need to make sure BTRFS_ORDERED_IOERR is set on the ordered
		 * extent, and mark the inode with the error if it wasn't
		 * already set.  Any error during writeback would have already
		 * set the mapping error, so we need to set it if we're the ones
		 * marking this ordered extent as failed.
		 */
		if (ret && !test_and_set_bit(BTRFS_ORDERED_IOERR,
					     &ordered_extent->flags))
			mapping_set_error(ordered_extent->inode->i_mapping, -EIO);

		if (truncated)
			unwritten_start += logical_len;
		clear_extent_uptodate(io_tree, unwritten_start, end, NULL);

		/* Drop extent maps for the part of the extent we didn't write. */
		btrfs_drop_extent_map_range(inode, unwritten_start, end, false);

		/*
		 * If the ordered extent had an IOERR or something else went
		 * wrong we need to return the space for this ordered extent
		 * back to the allocator.  We only free the extent in the
		 * truncated case if we didn't write out the extent at all.
		 *
		 * If we made it past insert_reserved_file_extent before we
		 * errored out then we don't need to do this as the accounting
		 * has already been done.
		 */
		if ((ret || !logical_len) &&
		    clear_reserved_extent &&
		    !test_bit(BTRFS_ORDERED_NOCOW, &ordered_extent->flags) &&
		    !test_bit(BTRFS_ORDERED_PREALLOC, &ordered_extent->flags)) {
			/*
			 * Discard the range before returning it back to the
			 * free space pool
			 */
			if (ret && btrfs_test_opt(fs_info, DISCARD_SYNC))
				btrfs_discard_extent(fs_info,
						ordered_extent->disk_bytenr,
						ordered_extent->disk_num_bytes,
						NULL);
			btrfs_free_reserved_extent(fs_info,
					ordered_extent->disk_bytenr,
					ordered_extent->disk_num_bytes, 1);
		}
	}

	/*
	 * This needs to be done to make sure anybody waiting knows we are done
	 * updating everything for this ordered extent.
	 */
	btrfs_remove_ordered_extent(inode, ordered_extent);

	/* once for us */
	btrfs_put_ordered_extent(ordered_extent);
	/* once for the tree */
	btrfs_put_ordered_extent(ordered_extent);

	return ret;
}

void btrfs_writepage_endio_finish_ordered(struct btrfs_inode *inode,
					  struct page *page, u64 start,
					  u64 end, bool uptodate)
{
	trace_btrfs_writepage_end_io_hook(inode, start, end, uptodate);

	btrfs_mark_ordered_io_finished(inode, page, start, end + 1 - start, uptodate);
}

/*
 * Verify the checksum for a single sector without any extra action that depend
 * on the type of I/O.
 */
int btrfs_check_sector_csum(struct btrfs_fs_info *fs_info, struct page *page,
			    u32 pgoff, u8 *csum, const u8 * const csum_expected)
{
	SHASH_DESC_ON_STACK(shash, fs_info->csum_shash);
	char *kaddr;

	ASSERT(pgoff + fs_info->sectorsize <= PAGE_SIZE);

	shash->tfm = fs_info->csum_shash;

	kaddr = kmap_local_page(page) + pgoff;
	crypto_shash_digest(shash, kaddr, fs_info->sectorsize, csum);
	kunmap_local(kaddr);

	if (memcmp(csum, csum_expected, fs_info->csum_size))
		return -EIO;
	return 0;
}

static u8 *btrfs_csum_ptr(const struct btrfs_fs_info *fs_info, u8 *csums, u64 offset)
{
	u64 offset_in_sectors = offset >> fs_info->sectorsize_bits;

	return csums + offset_in_sectors * fs_info->csum_size;
}

/*
 * Verify the checksum of a single data sector.
 *
 * @bbio:	btrfs_io_bio which contains the csum
 * @dev:	device the sector is on
 * @bio_offset:	offset to the beginning of the bio (in bytes)
 * @bv:		bio_vec to check
 *
 * Check if the checksum on a data block is valid.  When a checksum mismatch is
 * detected, report the error and fill the corrupted range with zero.
 *
 * Return %true if the sector is ok or had no checksum to start with, 