/* -*- mode: c; c-basic-offset: 8; -*-
 * vim: noexpandtab sw=8 ts=8 sts=0:
 *
 * dlmglue.c
 *
 * Code which implements an OCFS2 specific interface to our DLM.
 *
 * Copyright (C) 2003, 2004 Oracle.  All rights reserved.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 021110-1307, USA.
 */

#include <linux/types.h>
#include <linux/slab.h>
#include <linux/highmem.h>
#include <linux/mm.h>
#include <linux/kthread.h>
#include <linux/pagemap.h>
#include <linux/debugfs.h>
#include <linux/seq_file.h>
#include <linux/time.h>
#include <linux/quotaops.h>

#define MLOG_MASK_PREFIX ML_DLM_GLUE
#include <cluster/masklog.h>

#include "ocfs2.h"
#include "ocfs2_lockingver.h"

#include "alloc.h"
#include "dcache.h"
#include "dlmglue.h"
#include "extent_map.h"
#include "file.h"
#include "heartbeat.h"
#include "inode.h"
#include "journal.h"
#include "stackglue.h"
#include "slot_map.h"
#include "super.h"
#include "uptodate.h"
#include "quota.h"
#include "refcounttree.h"

#include "buffer_head_io.h"

struct ocfs2_mask_waiter {
	struct list_head	mw_item;
	int			mw_status;
	struct completion	mw_complete;
	unsigned long		mw_mask;
	unsigned long		mw_goal;
#ifdef CONFIG_OCFS2_FS_STATS
	unsigned long long 	mw_lock_start;
#endif
};

static struct ocfs2_super *ocfs2_get_dentry_osb(struct ocfs2_lock_res *lockres);
static struct ocfs2_super *ocfs2_get_inode_osb(struct ocfs2_lock_res *lockres);
static struct ocfs2_super *ocfs2_get_file_osb(struct ocfs2_lock_res *lockres);
static struct ocfs2_super *ocfs2_get_qinfo_osb(struct ocfs2_lock_res *lockres);

/*
 * Return value from ->downconvert_worker functions.
 *
 * These control the precise actions of ocfs2_unblock_lock()
 * and ocfs2_process_blocked_lock()
 *
 */
enum ocfs2_unblock_action {
	UNBLOCK_CONTINUE	= 0, /* Continue downconvert */
	UNBLOCK_CONTINUE_POST	= 1, /* Continue downconvert, fire
				      * ->post_unlock callback */
	UNBLOCK_STOP_POST	= 2, /* Do not downconvert, fire
				      * ->post_unlock() callback. */
};

struct ocfs2_unblock_ctl {
	int requeue;
	enum ocfs2_unblock_action unblock_action;
};

/* Lockdep class keys */
struct lock_class_key lockdep_keys[OCFS2_NUM_LOCK_TYPES];

static int ocfs2_check_meta_downconvert(struct ocfs2_lock_res *lockres,
					int new_level);
static void ocfs2_set_meta_lvb(struct ocfs2_lock_res *lockres);

static int ocfs2_data_convert_worker(struct ocfs2_lock_res *lockres,
				     int blocking);

static int ocfs2_dentry_convert_worker(struct ocfs2_lock_res *lockres,
				       int blocking);

static void ocfs2_dentry_post_unlock(struct ocfs2_super *osb,
				     struct ocfs2_lock_res *lockres);

static void ocfs2_set_qinfo_lvb(struct ocfs2_lock_res *lockres);

static int ocfs2_check_refcount_downconvert(struct ocfs2_lock_res *lockres,
					    int new_level);
static int ocfs2_refcount_convert_worker(struct ocfs2_lock_res *lockres,
					 int blocking);

#define mlog_meta_lvb(__level, __lockres) ocfs2_dump_meta_lvb_info(__level, __PRETTY_FUNCTION__, __LINE__, __lockres)

/* This aids in debugging situations where a bad LVB might be involved. */
static void ocfs2_dump_meta_lvb_info(u64 level,
				     const char *function,
				     unsigned int line,
				     struct ocfs2_lock_res *lockres)
{
	struct ocfs2_meta_lvb *lvb = ocfs2_dlm_lvb(&lockres->l_lksb);

	mlog(level, "LVB information for %s (called from %s:%u):\n",
	     lockres->l_name, function, line);
	mlog(level, "version: %u, clusters: %u, generation: 0x%x\n",
	     lvb->lvb_version, be32_to_cpu(lvb->lvb_iclusters),
	     be32_to_cpu(lvb->lvb_igeneration));
	mlog(level, "size: %llu, uid %u, gid %u, mode 0x%x\n",
	     (unsigned long long)be64_to_cpu(lvb->lvb_isize),
	     be32_to_cpu(lvb->lvb_iuid), be32_to_cpu(lvb->lvb_igid),
	     be16_to_cpu(lvb->lvb_imode));
	mlog(level, "nlink %u, atime_packed 0x%llx, ctime_packed 0x%llx, "
	     "mtime_packed 0x%llx iattr 0x%x\n", be16_to_cpu(lvb->lvb_inlink),
	     (long long)be64_to_cpu(lvb->lvb_iatime_packed),
	     (long long)be64_to_cpu(lvb->lvb_ictime_packed),
	     (long long)be64_to_cpu(lvb->lvb_imtime_packed),
	     be32_to_cpu(lvb->lvb_iattr));
}


/*
 * OCFS2 Lock Resource Operations
 *
 * These fine tune the behavior of the generic dlmglue locking infrastructure.
 *
 * The most basic of lock types can point ->l_priv to their respective
 * struct ocfs2_super and allow the default actions to manage things.
 *
 * Right now, each lock type also needs to implement an init function,
 * and trivial lock/unlock wrappers. ocfs2_simple_drop_lockres()
 * should be called when the lock is no longer needed (i.e., object
 * destruction time).
 */
struct ocfs2_lock_res_ops {
	/*
	 * Translate an ocfs2_lock_res * into an ocfs2_super *. Define
	 * this callback if ->l_priv is not an ocfs2_super pointer
	 */
	struct ocfs2_super * (*get_osb)(struct ocfs2_lock_res *);

	/*
	 * Optionally called in the downconvert thread after a
	 * successful downconvert. The lockres will not be referenced
	 * after this callback is called, so it is safe to free
	 * memory, etc.
	 *
	 * The exact semantics of when this is called are controlled
	 * by ->downconvert_worker()
	 */
	void (*post_unlock)(struct ocfs2_super *, struct ocfs2_lock_res *);

	/*
	 * Allow a lock type to add checks to determine whether it is
	 * safe to downconvert a lock. Return 0 to re-queue the
	 * downconvert at a later time, nonzero to continue.
	 *
	 * For most locks, the default checks that there are no
	 * incompatible holders are sufficient.
	 *
	 * Called with the lockres spinlock held.
	 */
	int (*check_downconvert)(struct ocfs2_lock_res *, int);

	/*
	 * Allows a lock type to populate the lock value block. This
	 * is called on downconvert, and when we drop a lock.
	 *
	 * Locks that want to use this should set LOCK_TYPE_USES_LVB
	 * in the flags field.
	 *
	 * Called with the lockres spinlock held.
	 */
	void (*set_lvb)(struct ocfs2_lock_res *);

	/*
	 * Called from the downconvert thread when it is determined
	 * that a lock will be downconverted. This is called without
	 * any locks held so the function can do work that might
	 * schedule (syncing out data, etc).
	 *
	 * This should return any one of the ocfs2_unblock_action
	 * values, depending on what it wants the thread to do.
	 */
	int (*downconvert_worker)(struct ocfs2_lock_res *, int);

	/*
	 * LOCK_TYPE_* flags which describe the specific requirements
	 * of a lock type. Descriptions of each individual flag follow.
	 */
	int flags;
};

/*
 * Some locks want to "refresh" potentially stale data when a
 * meaningful (PRMODE or EXMODE) lock level is first obtained. If this
 * flag is set, the OCFS2_LOCK_NEEDS_REFRESH flag will be set on the
 * individual lockres l_flags member from the ast function. It is
 * expected that the locking wrapper will clear the
 * OCFS2_LOCK_NEEDS_REFRESH flag when done.
 */
#define LOCK_TYPE_REQUIRES_REFRESH 0x1

/*
 * Indicate that a lock type makes use of the lock value block. The
 * ->set_lvb lock type callback must be defined.
 */
#define LOCK_TYPE_USES_LVB		0x2

static struct ocfs2_lock_res_ops ocfs2_inode_rw_lops = {
	.get_osb	= ocfs2_get_inode_osb,
	.flags		= 0,
};

static struct ocfs2_lock_res_ops ocfs2_inode_inode_lops = {
	.get_osb	= ocfs2_get_inode_osb,
	.check_downconvert = ocfs2_check_meta_downconvert,
	.set_lvb	= ocfs2_set_meta_lvb,
	.downconvert_worker = ocfs2_data_convert_worker,
	.flags		= LOCK_TYPE_REQUIRES_REFRESH|LOCK_TYPE_USES_LVB,
};

static struct ocfs2_lock_res_ops ocfs2_super_lops = {
	.flags		= LOCK_TYPE_REQUIRES_REFRESH,
};

static struct ocfs2_lock_res_ops ocfs2_rename_lops = {
	.flags		= 0,
};

static struct ocfs2_lock_res_ops ocfs2_nfs_sync_lops = {
	.flags		= 0,
};

static struct ocfs2_lock_res_ops ocfs2_orphan_scan_lops = {
	.flags		= LOCK_TYPE_REQUIRES_REFRESH|LOCK_TYPE_USES_LVB,
};

static struct ocfs2_lock_res_ops ocfs2_dentry_lops = {
	.get_osb	= ocfs2_get_dentry_osb,
	.post_unlock	= ocfs2_dentry_post_unlock,
	.downconvert_worker = ocfs2_dentry_convert_worker,
	.flags		= 0,
};

static struct ocfs2_lock_res_ops ocfs2_inode_open_lops = {
	.get_osb	= ocfs2_get_inode_osb,
	.flags		= 0,
};

static struct ocfs2_lock_res_ops ocfs2_flock_lops = {
	.get_osb	= ocfs2_get_file_osb,
	.flags		= 0,
};

static struct ocfs2_lock_res_ops ocfs2_qinfo_lops = {
	.set_lvb	= ocfs2_set_qinfo_lvb,
	.get_osb	= ocfs2_get_qinfo_osb,
	.flags		= LOCK_TYPE_REQUIRES_REFRESH | LOCK_TYPE_USES_LVB,
};

static struct ocfs2_lock_res_ops ocfs2_refcount_block_lops = {
	.check_downconvert = ocfs2_check_refcount_downconvert,
	.downconvert_worker = ocfs2_refcount_convert_worker,
	.flags		= 0,
};

static inline int ocfs2_is_inode_lock(struct ocfs2_lock_res *lockres)
{
	return lockres->l_type == OCFS2_LOCK_TYPE_META ||
		lockres->l_type == OCFS2_LOCK_TYPE_RW ||
		lockres->l_type == OCFS2_LOCK_TYPE_OPEN;
}

static inline struct ocfs2_lock_res *ocfs2_lksb_to_lock_res(struct ocfs2_dlm_lksb *lksb)
{
	return container_of(lksb, struct ocfs2_lock_res, l_lksb);
}

static inline struct inode *ocfs2_lock_res_inode(struct ocfs2_lock_res *lockres)
{
	BUG_ON(!ocfs2_is_inode_lock(lockres));

	return (struct inode *) lockres->l_priv;
}

static inline struct ocfs2_dentry_lock *ocfs2_lock_res_dl(struct ocfs2_lock_res *lockres)
{
	BUG_ON(lockres->l_type != OCFS2_LOCK_TYPE_DENTRY);

	return (struct ocfs2_dentry_lock *)lockres->l_priv;
}

static inline struct ocfs2_mem_dqinfo *ocfs2_lock_res_qinfo(struct ocfs2_lock_res *lockres)
{
	BUG_ON(lockres->l_type != OCFS2_LOCK_TYPE_QINFO);

	return (struct ocfs2_mem_dqinfo *)lockres->l_priv;
}

static inline struct ocfs2_refcount_tree *
ocfs2_lock_res_refcount_tree(struct ocfs2_lock_res *res)
{
	return container_of(res, struct ocfs2_refcount_tree, rf_lockres);
}

static inline struct ocfs2_super *ocfs2_get_lockres_osb(struct ocfs2_lock_res *lockres)
{
	if (lockres->l_ops->get_osb)
		return lockres->l_ops->get_osb(lockres);

	return (struct ocfs2_super *)lockres->l_priv;
}

static int ocfs2_lock_create(struct ocfs2_super *osb,
			     struct ocfs2_lock_res *lockres,
			     int level,
			     u32 dlm_flags);
static inline int ocfs2_may_continue_on_blocked_lock(struct ocfs2_lock_res *lockres,
						     int wanted);
static void __ocfs2_cluster_unlock(struct ocfs2_super *osb,
				   struct ocfs2_lock_res *lockres,
				   int level, unsigned long caller_ip);
static inline void ocfs2_cluster_unlock(struct ocfs2_super *osb,
					struct ocfs2_lock_res *lockres,
					int level)
{
	__ocfs2_cluster_unlock(osb, lockres, level, _RET_IP_);
}

static inline void ocfs2_generic_handle_downconvert_action(struct ocfs2_lock_res *lockres);
static inline void ocfs2_generic_handle_convert_action(struct ocfs2_lock_res *lockres);
static inline void ocfs2_generic_handle_attach_action(struct ocfs2_lock_res *lockres);
static int ocfs2_generic_handle_bast(struct ocfs2_lock_res *lockres, int level);
static void ocfs2_schedule_blocked_lock(struct ocfs2_super *osb,
					struct ocfs2_lock_res *lockres);
static inline void ocfs2_recover_from_dlm_error(struct ocfs2_lock_res *lockres,
						int convert);
#define ocfs2_log_dlm_error(_func, _err, _lockres) do {					\
	if ((_lockres)->l_type != OCFS2_LOCK_TYPE_DENTRY)				\
		mlog(ML_ERROR, "DLM error %d while calling %s on resource %s\n",	\
		     _err, _func, _lockres->l_name);					\
	else										\
		mlog(ML_ERROR, "DLM error %d while calling %s on resource %.*s%08x\n",	\
		     _err, _func, OCFS2_DENTRY_LOCK_INO_START - 1, (_lockres)->l_name,	\
		     (unsigned int)ocfs2_get_dentry_lock_ino(_lockres));		\
} while (0)
static int ocfs2_downconvert_thread(void *arg);
static void ocfs2_downconvert_on_unlock(struct ocfs2_super *osb,
					struct ocfs2_lock_res *lockres);
static int ocfs2_inode_lock_update(struct inode *inode,
				  struct buffer_head **bh);
static void ocfs2_drop_osb_locks(struct ocfs2_super *osb);
static inline int ocfs2_highest_compat_lock_level(int level);
static unsigned int ocfs2_prepare_downconvert(struct ocfs2_lock_res *lockres,
					      int new_level);
static int ocfs2_downconvert_lock(struct ocfs2_super *osb,
				  struct ocfs2_lock_res *lockres,
				  int new_level,
				  int lvb,
				  unsigned int generation);
static int ocfs2_prepare_cancel_convert(struct ocfs2_super *osb,
				        struct ocfs2_lock_res *lockres);
static int ocfs2_cancel_convert(struct ocfs2_super *osb,
				struct ocfs2_lock_res *lockres);


static void ocfs2_build_lock_name(enum ocfs2_lock_type type,
				  u64 blkno,
				  u32 generation,
				  char *name)
{
	int len;

	mlog_entry_void();

	BUG_ON(type >= OCFS2_NUM_LOCK_TYPES);

	len = snprintf(name, OCFS2_LOCK_ID_MAX_LEN, "%c%s%016llx%08x",
		       ocfs2_lock_type_char(type), OCFS2_LOCK_ID_PAD,
		       (long long)blkno, generation);

	BUG_ON(len != (OCFS2_LOCK_ID_MAX_LEN - 1));

	mlog(0, "built lock resource with name: %s\n", name);

	mlog_exit_void();
}

static DEFINE_SPINLOCK(ocfs2_dlm_tracking_lock);

static void ocfs2_add_lockres_tracking(struct ocfs2_lock_res *res,
				       struct ocfs2_dlm_debug *dlm_debug)
{
	mlog(0, "Add tracking for lockres %s\n", res->l_name);

	spin_lock(&ocfs2_dlm_tracking_lock);
	list_add(&res->l_debug_list, &dlm_debug->d_lockres_tracking);
	spin_unlock(&ocfs2_dlm_tracking_lock);
}

static void ocfs2_remove_lockres_tracking(struct ocfs2_lock_res *res)
{
	spin_lock(&ocfs2_dlm_tracking_lock);
	if (!list_empty(&res->l_debug_list))
		list_del_init(&res->l_debug_list);
	spin_unlock(&ocfs2_dlm_tracking_lock);
}

#ifdef CONFIG_OCFS2_FS_STATS
static void ocfs2_init_lock_stats(struct ocfs2_lock_res *res)
{
	res->l_lock_num_prmode = 0;
	res->l_lock_num_prmode_failed = 0;
	res->l_lock_total_prmode = 0;
	res->l_lock_max_prmode = 0;
	res->l_lock_num_exmode = 0;
	res->l_lock_num_exmode_failed = 0;
	res->l_lock_total_exmode = 0;
	res->l_lock_max_exmode = 0;
	res->l_lock_refresh = 0;
}

static void ocfs2_update_lock_stats(struct ocfs2_lock_res *res, int level,
				    struct ocfs2_mask_waiter *mw, int ret)
{
	unsigned long long *num, *sum;
	unsigned int *max, *failed;
	struct timespec ts = current_kernel_time();
	unsigned long long time = timespec_to_ns(&ts) - mw->mw_lock_start;

	if (level == LKM_PRMODE) {
		num = &res->l_lock_num_prmode;
		sum = &res->l_lock_total_prmode;
		max = &res->l_lock_max_prmode;
		failed = &res->l_lock_num_prmode_failed;
	} else if (level == LKM_EXMODE) {
		num = &res->l_lock_num_exmode;
		sum = &res->l_lock_total_exmode;
		max = &res->l_lock_max_exmode;
		failed = &res->l_lock_num_exmode_failed;
	} else
		return;

	(*num)++;
	(*sum) += time;
	if (time > *max)
		*max = time;
	if (ret)
		(*failed)++;
}

static inline void ocfs2_track_lock_refresh(struct ocfs2_lock_res *lockres)
{
	lockres->l_lock_refresh++;
}

static inline void ocfs2_init_start_time(struct ocfs2_mask_waiter *mw)
{
	struct timespec ts = current_kernel_time();
	mw->mw_lock_start = timespec_to_ns(&ts);
}
#else
static inline void ocfs2_init_lock_stats(struct ocfs2_lock_res *res)
{
}
static inline void ocfs2_update_lock_stats(struct ocfs2_lock_res *res,
			   int level, struct ocfs2_mask_waiter *mw, int ret)
{
}
static inline void ocfs2_track_lock_refresh(struct ocfs2_lock_res *lockres)
{
}
static inline void ocfs2_init_start_time(struct ocfs2_mask_waiter *mw)
{
}
#endif

static void ocfs2_lock_res_init_common(struct ocfs2_super *osb,
				       struct ocfs2_lock_res *res,
				       enum ocfs2_lock_type type,
				       struct ocfs2_lock_res_ops *ops,
				       void *priv)
{
	res->l_type          = type;
	res->l_ops           = ops;
	res->l_priv          = priv;

	res->l_level         = DLM_LOCK_IV;
	res->l_requested     = DLM_LOCK_IV;
	res->l_blocking      = DLM_LOCK_IV;
	res->l_action        = OCFS2_AST_INVALID;
	res->l_unlock_action = OCFS2_UNLOCK_INVALID;

	res->l_flags         = OCFS2_LOCK_INITIALIZED;

	ocfs2_add_lockres_tracking(res, osb->osb_dlm_debug);

	ocfs2_init_lock_stats(res);
#ifdef CONFIG_DEBUG_LOCK_ALLOC
	if (type != OCFS2_LOCK_TYPE_OPEN)
		lockdep_init_map(&res->l_lockdep_map, ocfs2_lock_type_strings[type],
				 &lockdep_keys[type], 0);
	else
		res->l_lockdep_map.key = NULL;
#endif
}

void ocfs2_lock_res_init_once(struct ocfs2_lock_res *res)
{
	/* This also clears out the lock status block */
	memset(res, 0, sizeof(struct ocfs2_lock_res));
	spin_lock_init(&res->l_lock);
	init_waitqueue_head(&res->l_event);
	INIT_LIST_HEAD(&res->l_blocked_list);
	INIT_LIST_HEAD(&res->l_mask_waiters);
}

void ocfs2_inode_lock_res_init(struct ocfs2_lock_res *res,
			       enum ocfs2_lock_type type,
			       unsigned int generation,
			       struct inode *inode)
{
	struct ocfs2_lock_res_ops *ops;

	switch(type) {
		case OCFS2_LOCK_TYPE_RW:
			ops = &ocfs2_inode_rw_lops;
			break;
		case OCFS2_LOCK_TYPE_META:
			ops = &ocfs2_inode_inode_lops;
			break;
		case OCFS2_LOCK_TYPE_OPEN:
			ops = &ocfs2_inode_open_lops;
			break;
		default:
			mlog_bug_on_msg(1, "type: %d\n", type);
			ops = NULL; /* thanks, gcc */
			break;
	};

	ocfs2_build_lock_name(type, OCFS2_I(inode)->ip_blkno,
			      generation, res->l_name);
	ocfs2_lock_res_init_common(OCFS2_SB(inode->i_sb), res, type, ops, inode);
}

static struct ocfs2_super *ocfs2_get_inode_osb(struct ocfs2_lock_res *lockres)
{
	struct inode *inode = ocfs2_lock_res_inode(lockres);

	return OCFS2_SB(inode->i_sb);
}

static struct ocfs2_super *ocfs2_get_qinfo_osb(struct ocfs2_lock_res *lockres)
{
	struct ocfs2_mem_dqinfo *info = lockres->l_priv;

	return OCFS2_SB(info->dqi_gi.dqi_sb);
}

static struct ocfs2_super *ocfs2_get_file_osb(struct ocfs2_lock_res *lockres)
{
	struct ocfs2_file_private *fp = lockres->l_priv;

	return OCFS2_SB(fp->fp_file->f_mapping->host->i_sb);
}

static __u64 ocfs2_get_dentry_lock_ino(struct ocfs2_lock_res *lockres)
{
	__be64 inode_blkno_be;

	memcpy(&inode_blkno_be, &lockres->l_name[OCFS2_DENTRY_LOCK_INO_START],
	       sizeof(__be64));

	return be64_to_cpu(inode_blkno_be);
}

static struct ocfs2_super *ocfs2_get_dentry_osb(struct ocfs2_lock_res *lockres)
{
	struct ocfs2_dentry_lock *dl = lockres->l_priv;

	return OCFS2_SB(dl->dl_inode->i_sb);
}

void ocfs2_dentry_lock_res_init(struct ocfs2_dentry_lock *dl,
				u64 parent, struct inode *inode)
{
	int len;
	u64 inode_blkno = OCFS2_I(inode)->ip_blkno;
	__be64 inode_blkno_be = cpu_to_be64(inode_blkno);
	struct ocfs2_lock_res *lockres = &dl->dl_lockres;

	ocfs2_lock_res_init_once(lockres);

	/*
	 * Unfortunately, the standard lock naming scheme won't work
	 * here because we have two 16 byte values to use. Instead,
	 * we'll stuff the inode number as a binary value. We still
	 * want error prints to show something without garbling the
	 * display, so drop a null byte in there before the inode
	 * number. A future version of OCFS2 will likely use all
	 * binary lock names. The stringified names have been a
	 * tremendous aid in debugging, but now that the debugfs
	 * interface exists, we can mangle things there if need be.
	 *
	 * NOTE: We also drop the standard "pad" value (the total lock
	 * name size stays the same though - the last part is all
	 * zeros due to the memset in ocfs2_lock_res_init_once()
	 */
	len = snprintf(lockres->l_name, OCFS2_DENTRY_LOCK_INO_START,
		       "%c%016llx",
		       ocfs2_lock_type_char(OCFS2_LOCK_TYPE_DENTRY),
		       (long long)parent);

	BUG_ON(len != (OCFS2_DENTRY_LOCK_INO_START - 1));

	memcpy(&lockres->l_name[OCFS2_DENTRY_LOCK_INO_START], &inode_blkno_be,
	       sizeof(__be64));

	ocfs2_lock_res_init_common(OCFS2_SB(inode->i_sb), lockres,
				   OCFS2_LOCK_TYPE_DENTRY, &ocfs2_dentry_lops,
				   dl);
}

static void ocfs2_super_lock_res_init(struct ocfs2_lock_res *res,
				      struct ocfs2_super *osb)
{
	/* Superblock lockres doesn't come from a slab so we call init
	 * once on it manually.  */
	ocfs2_lock_res_init_once(res);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_SUPER, OCFS2_SUPER_BLOCK_BLKNO,
			      0, res->l_name);
	ocfs2_lock_res_init_common(osb, res, OCFS2_LOCK_TYPE_SUPER,
				   &ocfs2_super_lops, osb);
}

static void ocfs2_rename_lock_res_init(struct ocfs2_lock_res *res,
				       struct ocfs2_super *osb)
{
	/* Rename lockres doesn't come from a slab so we call init
	 * once on it manually.  */
	ocfs2_lock_res_init_once(res);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_RENAME, 0, 0, res->l_name);
	ocfs2_lock_res_init_common(osb, res, OCFS2_LOCK_TYPE_RENAME,
				   &ocfs2_rename_lops, osb);
}

static void ocfs2_nfs_sync_lock_res_init(struct ocfs2_lock_res *res,
					 struct ocfs2_super *osb)
{
	/* nfs_sync lockres doesn't come from a slab so we call init
	 * once on it manually.  */
	ocfs2_lock_res_init_once(res);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_NFS_SYNC, 0, 0, res->l_name);
	ocfs2_lock_res_init_common(osb, res, OCFS2_LOCK_TYPE_NFS_SYNC,
				   &ocfs2_nfs_sync_lops, osb);
}

static void ocfs2_orphan_scan_lock_res_init(struct ocfs2_lock_res *res,
					    struct ocfs2_super *osb)
{
	ocfs2_lock_res_init_once(res);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_ORPHAN_SCAN, 0, 0, res->l_name);
	ocfs2_lock_res_init_common(osb, res, OCFS2_LOCK_TYPE_ORPHAN_SCAN,
				   &ocfs2_orphan_scan_lops, osb);
}

void ocfs2_file_lock_res_init(struct ocfs2_lock_res *lockres,
			      struct ocfs2_file_private *fp)
{
	struct inode *inode = fp->fp_file->f_mapping->host;
	struct ocfs2_inode_info *oi = OCFS2_I(inode);

	ocfs2_lock_res_init_once(lockres);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_FLOCK, oi->ip_blkno,
			      inode->i_generation, lockres->l_name);
	ocfs2_lock_res_init_common(OCFS2_SB(inode->i_sb), lockres,
				   OCFS2_LOCK_TYPE_FLOCK, &ocfs2_flock_lops,
				   fp);
	lockres->l_flags |= OCFS2_LOCK_NOCACHE;
}

void ocfs2_qinfo_lock_res_init(struct ocfs2_lock_res *lockres,
			       struct ocfs2_mem_dqinfo *info)
{
	ocfs2_lock_res_init_once(lockres);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_QINFO, info->dqi_gi.dqi_type,
			      0, lockres->l_name);
	ocfs2_lock_res_init_common(OCFS2_SB(info->dqi_gi.dqi_sb), lockres,
				   OCFS2_LOCK_TYPE_QINFO, &ocfs2_qinfo_lops,
				   info);
}

void ocfs2_refcount_lock_res_init(struct ocfs2_lock_res *lockres,
				  struct ocfs2_super *osb, u64 ref_blkno,
				  unsigned int generation)
{
	ocfs2_lock_res_init_once(lockres);
	ocfs2_build_lock_name(OCFS2_LOCK_TYPE_REFCOUNT, ref_blkno,
			      generation, lockres->l_name);
	ocfs2_lock_res_init_common(osb, lockres, OCFS2_LOCK_TYPE_REFCOUNT,
				   &ocfs2_refcount_block_lops, osb);
}

void ocfs2_lock_res_free(struct ocfs2_lock_res *res)
{
	mlog_entry_void();

	if (!(res->l_flags & OCFS2_LOCK_INITIALIZED))
		return;

	ocfs2_remove_lockres_tracking(res);

	mlog_bug_on_msg(!list_empty(&res->l_blocked_list),
			"Lockres %s is on the blocked list\n",
			res->l_name);
	mlog_bug_on_msg(!list_empty(&res->l_mask_waiters),
			"Lockres %s has mask waiters pending\n",
			res->l_name);
	mlog_bug_on_msg(spin_is_locked(&res->l_lock),
			"Lockres %s is locked\n",
			res->l_name);
	mlog_bug_on_msg(res->l_ro_holders,
			"Lockres %s has %u ro holders\n",
			res->l_name, res->l_ro_holders);
	mlog_bug_on_msg(res->l_ex_holders,
			"Lockres %s has %u ex holders\n",
			res->l_name, res->l_ex_holders);

	/* Need to clear out the lock status block for the dlm */
	memset(&res->l_lksb, 0, sizeof(res->l_lksb));

	res->l_flags = 0UL;
	mlog_exit_void();
}

static inline void ocfs2_inc_holders(struct ocfs2_lock_res *lockres,
				     int level)
{
	mlog_entry_void();

	BUG_ON(!lockres);

	switch(level) {
	case DLM_LOCK_EX:
		lockres->l_ex_holders++;
		break;
	case DLM_LOCK_PR:
		lockres->l_ro_holders++;
		break;
	default:
		BUG();
	}

	mlog_exit_void();
}

static inline void ocfs2_dec_holders(struct ocfs2_lock_res *lockres,
				     int level)
{
	mlog_entry_void();

	BUG_ON(!lockres);

	switch(level) {
	case DLM_LOCK_EX:
		BUG_ON(!lockres->l_ex_holders);
		lockres->l_ex_holders--;
		break;
	case DLM_LOCK_PR:
		BUG_ON(!lockres->l_ro_holders);
		lockres->l_ro_holders--;
		break;
	default:
		BUG();
	}
	mlog_exit_void();
}

/* WARNING: This function lives in a world where the only three lock
 * levels are EX, PR, and NL. It *will* have to be adjusted when more
 * lock types are added. */
static inline int ocfs2_highest_compat_lock_level(int level)
{
	int new_level = DLM_LOCK_EX;

	if (level == DLM_LOCK_EX)
		new_level = DLM_LOCK_NL;
	else if (level == DLM_LOCK_PR)
		new_level = DLM_LOCK_PR;
	return new_level;
}

static void lockres_set_flags(struct ocfs2_lock_res *lockres,
			      unsigned long newflags)
{
	struct ocfs2_mask_waiter *mw, *tmp;

 	assert_spin_locked(&lockres->l_lock);

	lockres->l_flags = newflags;

	list_for_each_entry_safe(mw, tmp, &lockres->l_mask_waiters, mw_item) {
		if ((lockres->l_flags & mw->mw_mask) != mw->mw_goal)
			continue;

		list_del_init(&mw->mw_item);
		mw->mw_status = 0;
		complete(&mw->mw_complete);
	}
}
static void lockres_or_flags(struct ocfs2_lock_res *lockres, unsigned long or)
{
	lockres_set_flags(lockres, lockres->l_flags | or);
}
static void lockres_clear_flags(struct ocfs2_lock_res *lockres,
				unsigned long clear)
{
	lockres_set_flags(lockres, lockres->l_flags & ~clear);
}

static inline void ocfs2_generic_handle_downconvert_action(struct ocfs2_lock_res *lockres)
{
	mlog_entry_void();

	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_BUSY));
	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_ATTACHED));
	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_BLOCKED));
	BUG_ON(lockres->l_blocking <= DLM_LOCK_NL);

	lockres->l_level = lockres->l_requested;
	if (lockres->l_level <=
	    ocfs2_highest_compat_lock_level(lockres->l_blocking)) {
		lockres->l_blocking = DLM_LOCK_NL;
		lockres_clear_flags(lockres, OCFS2_LOCK_BLOCKED);
	}
	lockres_clear_flags(lockres, OCFS2_LOCK_BUSY);

	mlog_exit_void();
}

static inline void ocfs2_generic_handle_convert_action(struct ocfs2_lock_res *lockres)
{
	mlog_entry_void();

	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_BUSY));
	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_ATTACHED));

	/* Convert from RO to EX doesn't really need anything as our
	 * information is already up to data. Convert from NL to
	 * *anything* however should mark ourselves as needing an
	 * update */
	if (lockres->l_level == DLM_LOCK_NL &&
	    lockres->l_ops->flags & LOCK_TYPE_REQUIRES_REFRESH)
		lockres_or_flags(lockres, OCFS2_LOCK_NEEDS_REFRESH);

	lockres->l_level = lockres->l_requested;

	/*
	 * We set the OCFS2_LOCK_UPCONVERT_FINISHING flag before clearing
	 * the OCFS2_LOCK_BUSY flag to prevent the dc thread from
	 * downconverting the lock before the upconvert has fully completed.
	 */
	lockres_or_flags(lockres, OCFS2_LOCK_UPCONVERT_FINISHING);

	lockres_clear_flags(lockres, OCFS2_LOCK_BUSY);

	mlog_exit_void();
}

static inline void ocfs2_generic_handle_attach_action(struct ocfs2_lock_res *lockres)
{
	mlog_entry_void();

	BUG_ON((!(lockres->l_flags & OCFS2_LOCK_BUSY)));
	BUG_ON(lockres->l_flags & OCFS2_LOCK_ATTACHED);

	if (lockres->l_requested > DLM_LOCK_NL &&
	    !(lockres->l_flags & OCFS2_LOCK_LOCAL) &&
	    lockres->l_ops->flags & LOCK_TYPE_REQUIRES_REFRESH)
		lockres_or_flags(lockres, OCFS2_LOCK_NEEDS_REFRESH);

	lockres->l_level = lockres->l_requested;
	lockres_or_flags(lockres, OCFS2_LOCK_ATTACHED);
	lockres_clear_flags(lockres, OCFS2_LOCK_BUSY);

	mlog_exit_void();
}

static int ocfs2_generic_handle_bast(struct ocfs2_lock_res *lockres,
				     int level)
{
	int needs_downconvert = 0;
	mlog_entry_void();

	assert_spin_locked(&lockres->l_lock);

	if (level > lockres->l_blocking) {
		/* only schedule a downconvert if we haven't already scheduled
		 * one that goes low enough to satisfy the level we're
		 * blocking.  this also catches the case where we get
		 * duplicate BASTs */
		if (ocfs2_highest_compat_lock_level(level) <
		    ocfs2_highest_compat_lock_level(lockres->l_blocking))
			needs_downconvert = 1;

		lockres->l_blocking = level;
	}

	mlog(ML_BASTS, "lockres %s, block %d, level %d, l_block %d, dwn %d\n",
	     lockres->l_name, level, lockres->l_level, lockres->l_blocking,
	     needs_downconvert);

	if (needs_downconvert)
		lockres_or_flags(lockres, OCFS2_LOCK_BLOCKED);

	mlog_exit(needs_downconvert);
	return needs_downconvert;
}

/*
 * OCFS2_LOCK_PENDING and l_pending_gen.
 *
 * Why does OCFS2_LOCK_PENDING exist?  To close a race between setting
 * OCFS2_LOCK_BUSY and calling ocfs2_dlm_lock().  See ocfs2_unblock_lock()
 * for more details on the race.
 *
 * OCFS2_LOCK_PENDING closes the race quite nicely.  However, it introduces
 * a race on itself.  In o2dlm, we can get the ast before ocfs2_dlm_lock()
 * returns.  The ast clears OCFS2_LOCK_BUSY, and must therefore clear
 * OCFS2_LOCK_PENDING at the same time.  When ocfs2_dlm_lock() returns,
 * the caller is going to try to clear PENDING again.  If nothing else is
 * happening, __lockres_clear_pending() sees PENDING is unset and does
 * nothing.
 *
 * But what if another path (eg downconvert thread) has just started a
 * new locking action?  The other path has re-set PENDING.  Our path
 * cannot clear PENDING, because that will re-open the original race
 * window.
 *
 * [Example]
 *
 * ocfs2_meta_lock()
 *  ocfs2_cluster_lock()
 *   set BUSY
 *   set PENDING
 *   drop l_lock
 *   ocfs2_dlm_lock()
 *    ocfs2_locking_ast()		ocfs2_downconvert_thread()
 *     clear PENDING			 ocfs2_unblock_lock()
 *					  take_l_lock
 *					  !BUSY
 *					  ocfs2_prepare_downconvert()
 *					   set BUSY
 *					   set PENDING
 *					  drop l_lock
 *   take l_lock
 *   clear PENDING
 *   drop l_lock
 *			<window>
 *					  ocfs2_dlm_lock()
 *
 * So as you can see, we now have a window where l_lock is not held,
 * PENDING is not set, and ocfs2_dlm_lock() has not been called.
 *
 * The core problem is that ocfs2_cluster_lock() has cleared the PENDING
 * set by ocfs2_prepare_downconvert().  That wasn't nice.
 *
 * To solve this we introduce l_pending_gen.  A call to
 * lockres_clear_pending() will only do so when it is passed a generation
 * number that matches the lockres.  lockres_set_pending() will return the
 * current generation number.  When ocfs2_cluster_lock() goes to clear
 * PENDING, it passes the generation it got from set_pending().  In our
 * example above, the generation numbers will *not* match.  Thus,
 * ocfs2_cluster_lock() will not clear the PENDING set by
 * ocfs2_prepare_downconvert().
 */

/* Unlocked version for ocfs2_locking_ast() */
static void __lockres_clear_pending(struct ocfs2_lock_res *lockres,
				    unsigned int generation,
				    struct ocfs2_super *osb)
{
	assert_spin_locked(&lockres->l_lock);

	/*
	 * The ast and locking functions can race us here.  The winner
	 * will clear pending, the loser will not.
	 */
	if (!(lockres->l_flags & OCFS2_LOCK_PENDING) ||
	    (lockres->l_pending_gen != generation))
		return;

	lockres_clear_flags(lockres, OCFS2_LOCK_PENDING);
	lockres->l_pending_gen++;

	/*
	 * The downconvert thread may have skipped us because we
	 * were PENDING.  Wake it up.
	 */
	if (lockres->l_flags & OCFS2_LOCK_BLOCKED)
		ocfs2_wake_downconvert_thread(osb);
}

/* Locked version for callers of ocfs2_dlm_lock() */
static void lockres_clear_pending(struct ocfs2_lock_res *lockres,
				  unsigned int generation,
				  struct ocfs2_super *osb)
{
	unsigned long flags;

	spin_lock_irqsave(&lockres->l_lock, flags);
	__lockres_clear_pending(lockres, generation, osb);
	spin_unlock_irqrestore(&lockres->l_lock, flags);
}

static unsigned int lockres_set_pending(struct ocfs2_lock_res *lockres)
{
	assert_spin_locked(&lockres->l_lock);
	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_BUSY));

	lockres_or_flags(lockres, OCFS2_LOCK_PENDING);

	return lockres->l_pending_gen;
}

static void ocfs2_blocking_ast(struct ocfs2_dlm_lksb *lksb, int level)
{
	struct ocfs2_lock_res *lockres = ocfs2_lksb_to_lock_res(lksb);
	struct ocfs2_super *osb = ocfs2_get_lockres_osb(lockres);
	int needs_downconvert;
	unsigned long flags;

	BUG_ON(level <= DLM_LOCK_NL);

	mlog(ML_BASTS, "BAST fired for lockres %s, blocking %d, level %d, "
	     "type %s\n", lockres->l_name, level, lockres->l_level,
	     ocfs2_lock_type_string(lockres->l_type));

	/*
	 * We can skip the bast for locks which don't enable caching -
	 * they'll be dropped at the earliest possible time anyway.
	 */
	if (lockres->l_flags & OCFS2_LOCK_NOCACHE)
		return;

	spin_lock_irqsave(&lockres->l_lock, flags);
	needs_downconvert = ocfs2_generic_handle_bast(lockres, level);
	if (needs_downconvert)
		ocfs2_schedule_blocked_lock(osb, lockres);
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	wake_up(&lockres->l_event);

	ocfs2_wake_downconvert_thread(osb);
}

static void ocfs2_locking_ast(struct ocfs2_dlm_lksb *lksb)
{
	struct ocfs2_lock_res *lockres = ocfs2_lksb_to_lock_res(lksb);
	struct ocfs2_super *osb = ocfs2_get_lockres_osb(lockres);
	unsigned long flags;
	int status;

	spin_lock_irqsave(&lockres->l_lock, flags);

	status = ocfs2_dlm_lock_status(&lockres->l_lksb);

	if (status == -EAGAIN) {
		lockres_clear_flags(lockres, OCFS2_LOCK_BUSY);
		goto out;
	}

	if (status) {
		mlog(ML_ERROR, "lockres %s: lksb status value of %d!\n",
		     lockres->l_name, status);
		spin_unlock_irqrestore(&lockres->l_lock, flags);
		return;
	}

	mlog(ML_BASTS, "AST fired for lockres %s, action %d, unlock %d, "
	     "level %d => %d\n", lockres->l_name, lockres->l_action,
	     lockres->l_unlock_action, lockres->l_level, lockres->l_requested);

	switch(lockres->l_action) {
	case OCFS2_AST_ATTACH:
		ocfs2_generic_handle_attach_action(lockres);
		lockres_clear_flags(lockres, OCFS2_LOCK_LOCAL);
		break;
	case OCFS2_AST_CONVERT:
		ocfs2_generic_handle_convert_action(lockres);
		break;
	case OCFS2_AST_DOWNCONVERT:
		ocfs2_generic_handle_downconvert_action(lockres);
		break;
	default:
		mlog(ML_ERROR, "lockres %s: AST fired with invalid action: %u, "
		     "flags 0x%lx, unlock: %u\n",
		     lockres->l_name, lockres->l_action, lockres->l_flags,
		     lockres->l_unlock_action);
		BUG();
	}
out:
	/* set it to something invalid so if we get called again we
	 * can catch it. */
	lockres->l_action = OCFS2_AST_INVALID;

	/* Did we try to cancel this lock?  Clear that state */
	if (lockres->l_unlock_action == OCFS2_UNLOCK_CANCEL_CONVERT)
		lockres->l_unlock_action = OCFS2_UNLOCK_INVALID;

	/*
	 * We may have beaten the locking functions here.  We certainly
	 * know that dlm_lock() has been called :-)
	 * Because we can't have two lock calls in flight at once, we
	 * can use lockres->l_pending_gen.
	 */
	__lockres_clear_pending(lockres, lockres->l_pending_gen,  osb);

	wake_up(&lockres->l_event);
	spin_unlock_irqrestore(&lockres->l_lock, flags);
}

static void ocfs2_unlock_ast(struct ocfs2_dlm_lksb *lksb, int error)
{
	struct ocfs2_lock_res *lockres = ocfs2_lksb_to_lock_res(lksb);
	unsigned long flags;

	mlog_entry_void();

	mlog(ML_BASTS, "UNLOCK AST fired for lockres %s, action = %d\n",
	     lockres->l_name, lockres->l_unlock_action);

	spin_lock_irqsave(&lockres->l_lock, flags);
	if (error) {
		mlog(ML_ERROR, "Dlm passes error %d for lock %s, "
		     "unlock_action %d\n", error, lockres->l_name,
		     lockres->l_unlock_action);
		spin_unlock_irqrestore(&lockres->l_lock, flags);
		mlog_exit_void();
		return;
	}

	switch(lockres->l_unlock_action) {
	case OCFS2_UNLOCK_CANCEL_CONVERT:
		mlog(0, "Cancel convert success for %s\n", lockres->l_name);
		lockres->l_action = OCFS2_AST_INVALID;
		/* Downconvert thread may have requeued this lock, we
		 * need to wake it. */
		if (lockres->l_flags & OCFS2_LOCK_BLOCKED)
			ocfs2_wake_downconvert_thread(ocfs2_get_lockres_osb(lockres));
		break;
	case OCFS2_UNLOCK_DROP_LOCK:
		lockres->l_level = DLM_LOCK_IV;
		break;
	default:
		BUG();
	}

	lockres_clear_flags(lockres, OCFS2_LOCK_BUSY);
	lockres->l_unlock_action = OCFS2_UNLOCK_INVALID;
	wake_up(&lockres->l_event);
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	mlog_exit_void();
}

/*
 * This is the filesystem locking protocol.  It provides the lock handling
 * hooks for the underlying DLM.  It has a maximum version number.
 * The version number allows interoperability with systems running at
 * the same major number and an equal or smaller minor number.
 *
 * Whenever the filesystem does new things with locks (adds or removes a
 * lock, orders them differently, does different things underneath a lock),
 * the version must be changed.  The protocol is negotiated when joining
 * the dlm domain.  A node may join the domain if its major version is
 * identical to all other nodes and its minor version is greater than
 * or equal to all other nodes.  When its minor version is greater than
 * the other nodes, it will run at the minor version specified by the
 * other nodes.
 *
 * If a locking change is made that will not be compatible with older
 * versions, the major number must be increased and the minor version set
 * to zero.  If a change merely adds a behavior that can be disabled when
 * speaking to older versions, the minor version must be increased.  If a
 * change adds a fully backwards compatible change (eg, LVB changes that
 * are just ignored by older versions), the version does not need to be
 * updated.
 */
static struct ocfs2_locking_protocol lproto = {
	.lp_max_version = {
		.pv_major = OCFS2_LOCKING_PROTOCOL_MAJOR,
		.pv_minor = OCFS2_LOCKING_PROTOCOL_MINOR,
	},
	.lp_lock_ast		= ocfs2_locking_ast,
	.lp_blocking_ast	= ocfs2_blocking_ast,
	.lp_unlock_ast		= ocfs2_unlock_ast,
};

void ocfs2_set_locking_protocol(void)
{
	ocfs2_stack_glue_set_max_proto_version(&lproto.lp_max_version);
}

static inline void ocfs2_recover_from_dlm_error(struct ocfs2_lock_res *lockres,
						int convert)
{
	unsigned long flags;

	mlog_entry_void();
	spin_lock_irqsave(&lockres->l_lock, flags);
	lockres_clear_flags(lockres, OCFS2_LOCK_BUSY);
	lockres_clear_flags(lockres, OCFS2_LOCK_UPCONVERT_FINISHING);
	if (convert)
		lockres->l_action = OCFS2_AST_INVALID;
	else
		lockres->l_unlock_action = OCFS2_UNLOCK_INVALID;
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	wake_up(&lockres->l_event);
	mlog_exit_void();
}

/* Note: If we detect another process working on the lock (i.e.,
 * OCFS2_LOCK_BUSY), we'll bail out returning 0. It's up to the caller
 * to do the right thing in that case.
 */
static int ocfs2_lock_create(struct ocfs2_super *osb,
			     struct ocfs2_lock_res *lockres,
			     int level,
			     u32 dlm_flags)
{
	int ret = 0;
	unsigned long flags;
	unsigned int gen;

	mlog_entry_void();

	mlog(0, "lock %s, level = %d, flags = %u\n", lockres->l_name, level,
	     dlm_flags);

	spin_lock_irqsave(&lockres->l_lock, flags);
	if ((lockres->l_flags & OCFS2_LOCK_ATTACHED) ||
	    (lockres->l_flags & OCFS2_LOCK_BUSY)) {
		spin_unlock_irqrestore(&lockres->l_lock, flags);
		goto bail;
	}

	lockres->l_action = OCFS2_AST_ATTACH;
	lockres->l_requested = level;
	lockres_or_flags(lockres, OCFS2_LOCK_BUSY);
	gen = lockres_set_pending(lockres);
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	ret = ocfs2_dlm_lock(osb->cconn,
			     level,
			     &lockres->l_lksb,
			     dlm_flags,
			     lockres->l_name,
			     OCFS2_LOCK_ID_MAX_LEN - 1);
	lockres_clear_pending(lockres, gen, osb);
	if (ret) {
		ocfs2_log_dlm_error("ocfs2_dlm_lock", ret, lockres);
		ocfs2_recover_from_dlm_error(lockres, 1);
	}

	mlog(0, "lock %s, return from ocfs2_dlm_lock\n", lockres->l_name);

bail:
	mlog_exit(ret);
	return ret;
}

static inline int ocfs2_check_wait_flag(struct ocfs2_lock_res *lockres,
					int flag)
{
	unsigned long flags;
	int ret;

	spin_lock_irqsave(&lockres->l_lock, flags);
	ret = lockres->l_flags & flag;
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	return ret;
}

static inline void ocfs2_wait_on_busy_lock(struct ocfs2_lock_res *lockres)

{
	wait_event(lockres->l_event,
		   !ocfs2_check_wait_flag(lockres, OCFS2_LOCK_BUSY));
}

static inline void ocfs2_wait_on_refreshing_lock(struct ocfs2_lock_res *lockres)

{
	wait_event(lockres->l_event,
		   !ocfs2_check_wait_flag(lockres, OCFS2_LOCK_REFRESHING));
}

/* predict what lock level we'll be dropping down to on behalf
 * of another node, and return true if the currently wanted
 * level will be compatible with it. */
static inline int ocfs2_may_continue_on_blocked_lock(struct ocfs2_lock_res *lockres,
						     int wanted)
{
	BUG_ON(!(lockres->l_flags & OCFS2_LOCK_BLOCKED));

	return wanted <= ocfs2_highest_compat_lock_level(lockres->l_blocking);
}

static void ocfs2_init_mask_waiter(struct ocfs2_mask_waiter *mw)
{
	INIT_LIST_HEAD(&mw->mw_item);
	init_completion(&mw->mw_complete);
	ocfs2_init_start_time(mw);
}

static int ocfs2_wait_for_mask(struct ocfs2_mask_waiter *mw)
{
	wait_for_completion(&mw->mw_complete);
	/* Re-arm the completion in case we want to wait on it again */
	INIT_COMPLETION(mw->mw_complete);
	return mw->mw_status;
}

static void lockres_add_mask_waiter(struct ocfs2_lock_res *lockres,
				    struct ocfs2_mask_waiter *mw,
				    unsigned long mask,
				    unsigned long goal)
{
	BUG_ON(!list_empty(&mw->mw_item));

	assert_spin_locked(&lockres->l_lock);

	list_add_tail(&mw->mw_item, &lockres->l_mask_waiters);
	mw->mw_mask = mask;
	mw->mw_goal = goal;
}

/* returns 0 if the mw that was removed was already satisfied, -EBUSY
 * if the mask still hadn't reached its goal */
static int lockres_remove_mask_waiter(struct ocfs2_lock_res *lockres,
				      struct ocfs2_mask_waiter *mw)
{
	unsigned long flags;
	int ret = 0;

	spin_lock_irqsave(&lockres->l_lock, flags);
	if (!list_empty(&mw->mw_item)) {
		if ((lockres->l_flags & mw->mw_mask) != mw->mw_goal)
			ret = -EBUSY;

		list_del_init(&mw->mw_item);
		init_completion(&mw->mw_complete);
	}
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	return ret;

}

static int ocfs2_wait_for_mask_interruptible(struct ocfs2_mask_waiter *mw,
					     struct ocfs2_lock_res *lockres)
{
	int ret;

	ret = wait_for_completion_interruptible(&mw->mw_complete);
	if (ret)
		lockres_remove_mask_waiter(lockres, mw);
	else
		ret = mw->mw_status;
	/* Re-arm the completion in case we want to wait on it again */
	INIT_COMPLETION(mw->mw_complete);
	return ret;
}

static int __ocfs2_cluster_lock(struct ocfs2_super *osb,
				struct ocfs2_lock_res *lockres,
				int level,
				u32 lkm_flags,
				int arg_flags,
				int l_subclass,
				unsigned long caller_ip)
{
	struct ocfs2_mask_waiter mw;
	int wait, catch_signals = !(osb->s_mount_opt & OCFS2_MOUNT_NOINTR);
	int ret = 0; /* gcc doesn't realize wait = 1 guarantees ret is set */
	unsigned long flags;
	unsigned int gen;
	int noqueue_attempted = 0;

	mlog_entry_void();

	ocfs2_init_mask_waiter(&mw);

	if (lockres->l_ops->flags & LOCK_TYPE_USES_LVB)
		lkm_flags |= DLM_LKF_VALBLK;

again:
	wait = 0;

	spin_lock_irqsave(&lockres->l_lock, flags);

	if (catch_signals && signal_pending(current)) {
		ret = -ERESTARTSYS;
		goto unlock;
	}

	mlog_bug_on_msg(lockres->l_flags & OCFS2_LOCK_FREEING,
			"Cluster lock called on freeing lockres %s! flags "
			"0x%lx\n", lockres->l_name, lockres->l_flags);

	/* We only compare against the currently granted level
	 * here. If the lock is blocked waiting on a downconvert,
	 * we'll get caught below. */
	if (lockres->l_flags & OCFS2_LOCK_BUSY &&
	    level > lockres->l_level) {
		/* is someone sitting in dlm_lock? If so, wait on
		 * them. */
		lockres_add_mask_waiter(lockres, &mw, OCFS2_LOCK_BUSY, 0);
		wait = 1;
		goto unlock;
	}

	if (lockres->l_flags & OCFS2_LOCK_UPCONVERT_FINISHING) {
		/*
		 * We've upconverted. If the lock now has a level we can
		 * work with, we take it. If, however, the lock is not at the
		 * required level, we go thru the full cycle. One way this could
		 * happen is if a process requesting an upconvert to PR is
		 * closely followed by another requesting upconvert to an EX.
		 * If the process requesting EX lands here, we want it to
		 * continue attempting to upconvert and let the process
		 * requesting PR take the lock.
		 * If multiple processes request upconvert to PR, the first one
		 * here will take the lock. The others will have to go thru the
		 * OCFS2_LOCK_BLOCKED check to ensure that there is no pending
		 * downconvert request.
		 */
		if (level <= lockres->l_level)
			goto update_holders;
	}

	if (lockres->l_flags & OCFS2_LOCK_BLOCKED &&
	    !ocfs2_may_continue_on_blocked_lock(lockres, level)) {
		/* is the lock is currently blocked on behalf of
		 * another node */
		lockres_add_mask_waiter(lockres, &mw, OCFS2_LOCK_BLOCKED, 0);
		wait = 1;
		goto unlock;
	}

	if (level > lockres->l_level) {
		if (noqueue_attempted > 0) {
			ret = -EAGAIN;
			goto unlock;
		}
		if (lkm_flags & DLM_LKF_NOQUEUE)
			noqueue_attempted = 1;

		if (lockres->l_action != OCFS2_AST_INVALID)
			mlog(ML_ERROR, "lockres %s has action %u pending\n",
			     lockres->l_name, lockres->l_action);

		if (!(lockres->l_flags & OCFS2_LOCK_ATTACHED)) {
			lockres->l_action = OCFS2_AST_ATTACH;
			lkm_flags &= ~DLM_LKF_CONVERT;
		} else {
			lockres->l_action = OCFS2_AST_CONVERT;
			lkm_flags |= DLM_LKF_CONVERT;
		}

		lockres->l_requested = level;
		lockres_or_flags(lockres, OCFS2_LOCK_BUSY);
		gen = lockres_set_pending(lockres);
		spin_unlock_irqrestore(&lockres->l_lock, flags);

		BUG_ON(level == DLM_LOCK_IV);
		BUG_ON(level == DLM_LOCK_NL);

		mlog(ML_BASTS, "lockres %s, convert from %d to %d\n",
		     lockres->l_name, lockres->l_level, level);

		/* call dlm_lock to upgrade lock now */
		ret = ocfs2_dlm_lock(osb->cconn,
				     level,
				     &lockres->l_lksb,
				     lkm_flags,
				     lockres->l_name,
				     OCFS2_LOCK_ID_MAX_LEN - 1);
		lockres_clear_pending(lockres, gen, osb);
		if (ret) {
			if (!(lkm_flags & DLM_LKF_NOQUEUE) ||
			    (ret != -EAGAIN)) {
				ocfs2_log_dlm_error("ocfs2_dlm_lock",
						    ret, lockres);
			}
			ocfs2_recover_from_dlm_error(lockres, 1);
			goto out;
		}

		mlog(0, "lock %s, successful return from ocfs2_dlm_lock\n",
		     lockres->l_name);

		/* At this point we've gone inside the dlm and need to
		 * complete our work regardless. */
		catch_signals = 0;

		/* wait for busy to clear and carry on */
		goto again;
	}

update_holders:
	/* Ok, if we get here then we're good to go. */
	ocfs2_inc_holders(lockres, level);

	ret = 0;
unlock:
	lockres_clear_flags(lockres, OCFS2_LOCK_UPCONVERT_FINISHING);

	spin_unlock_irqrestore(&lockres->l_lock, flags);
out:
	/*
	 * This is helping work around a lock inversion between the page lock
	 * and dlm locks.  One path holds the page lock while calling aops
	 * which block acquiring dlm locks.  The voting thread holds dlm
	 * locks while acquiring page locks while down converting data locks.
	 * This block is helping an aop path notice the inversion and back
	 * off to unlock its page lock before trying the dlm lock again.
	 */
	if (wait && arg_flags & OCFS2_LOCK_NONBLOCK &&
	    mw.mw_mask & (OCFS2_LOCK_BUSY|OCFS2_LOCK_BLOCKED)) {
		wait = 0;
		if (lockres_remove_mask_waiter(lockres, &mw))
			ret = -EAGAIN;
		else
			goto again;
	}
	if (wait) {
		ret = ocfs2_wait_for_mask(&mw);
		if (ret == 0)
			goto again;
		mlog_errno(ret);
	}
	ocfs2_update_lock_stats(lockres, level, &mw, ret);

#ifdef CONFIG_DEBUG_LOCK_ALLOC
	if (!ret && lockres->l_lockdep_map.key != NULL) {
		if (level == DLM_LOCK_PR)
			rwsem_acquire_read(&lockres->l_lockdep_map, l_subclass,
				!!(arg_flags & OCFS2_META_LOCK_NOQUEUE),
				caller_ip);
		else
			rwsem_acquire(&lockres->l_lockdep_map, l_subclass,
				!!(arg_flags & OCFS2_META_LOCK_NOQUEUE),
				caller_ip);
	}
#endif
	mlog_exit(ret);
	return ret;
}

static inline int ocfs2_cluster_lock(struct ocfs2_super *osb,
				     struct ocfs2_lock_res *lockres,
				     int level,
				     u32 lkm_flags,
				     int arg_flags)
{
	return __ocfs2_cluster_lock(osb, lockres, level, lkm_flags, arg_flags,
				    0, _RET_IP_);
}


static void __ocfs2_cluster_unlock(struct ocfs2_super *osb,
				   struct ocfs2_lock_res *lockres,
				   int level,
				   unsigned long caller_ip)
{
	unsigned long flags;

	mlog_entry_void();
	spin_lock_irqsave(&lockres->l_lock, flags);
	ocfs2_dec_holders(lockres, level);
	ocfs2_downconvert_on_unlock(osb, lockres);
	spin_unlock_irqrestore(&lockres->l_lock, flags);
#ifdef CONFIG_DEBUG_LOCK_ALLOC
	if (lockres->l_lockdep_map.key != NULL)
		rwsem_release(&lockres->l_lockdep_map, 1, caller_ip);
#endif
	mlog_exit_void();
}

static int ocfs2_create_new_lock(struct ocfs2_super *osb,
				 struct ocfs2_lock_res *lockres,
				 int ex,
				 int local)
{
	int level =  ex ? DLM_LOCK_EX : DLM_LOCK_PR;
	unsigned long flags;
	u32 lkm_flags = local ? DLM_LKF_LOCAL : 0;

	spin_lock_irqsave(&lockres->l_lock, flags);
	BUG_ON(lockres->l_flags & OCFS2_LOCK_ATTACHED);
	lockres_or_flags(lockres, OCFS2_LOCK_LOCAL);
	spin_unlock_irqrestore(&lockres->l_lock, flags);

	return ocfs2_lock_create(osb, lockres, level, lkm_flags);
}

/* Grants us an EX lock on the data and metadata resources, skipping
 * the normal cluster directory lookup. Use this ONLY on newly created
 * inodes which other nodes can't possibly see, and which haven't been
 * hashed in the inode hash yet. This can give us a good performance
 * increase as it'll skip the network broadcast normally associated
 * with creating a new lock resource. */
int ocfs2_create_new_inode_locks(struct inode *inode)
{
	int ret;
	struct ocfs2_super *osb = OCFS2_SB(inode->i_sb);

	BUG_ON(!inode);
	BUG_ON(!ocfs2_inode_is_new(inode));

	mlog_entry_void();

	mlog(0, "Inode %llu\n", (unsigned long long)OCFS2_I(inode)->ip_blkno);

	/* NOTE: That we don't increment any of the holder counts, nor
	 * do we add anything to a journal handle. Since this is
	 * supposed to be a new inode which the cluster doesn't know
	 * about yet, there is no need to.  As far as the LVB handling
	 * is concerned, this is basically like acquiring an EX lock
	 * on a resource which has an invalid one -- we'll set it
	 * valid when we release the EX. */

	ret = ocfs2_create_new_lock(osb, &OCFS2_I(inode)->ip_rw_lockres, 1, 1);
	if (ret) {
		mlog_errno(ret);
		goto bail;
	}

	/*
	 * We don't want to use DLM_LKF_LOCAL on a meta data lock as they
	 * don't use a generation in their lock names.
	 */
	ret = ocfs2_create_new_lock(osb, &OCFS2_I(inode)->ip_inode_lockres, 1, 0);
	if (ret) {
		mlog_errno(ret);
		goto bail;
	}

	ret = ocfs2_create_new_lock(osb, &OCFS2_I(inode)->ip_open_lockres, 0, 0);
	if (ret) {
		mlog_errno(ret);
		goto bail;
	}

bail:
	mlog_exit(ret);
	return ret;
}

int ocfs2_rw_lock(struct inode *inode, int write)
{
	int status, level;
	struct ocfs2_lock_res *lockres;
	struct ocfs2_super *osb = OCFS2_SB(inode->i_sb);

	BUG_ON(!inode);

	mlog_entry_void();

	mlog(0, "inode %llu take %s RW lock\n",
	     (unsigned long long)OCFS2_I(inode)->ip_blkno,
	     write ? "EXMODE" : "PRMODE");

	if (ocfs2_mount_local(osb)) {
		mlog_exit(0);
		return 0;
	}

	lockres = &OCFS2_I(inode)->ip_rw_lockres;

	level = write ? DLM_LOCK_EX : DLM_LOCK_PR;

	status = ocfs2_cluster_lock(OCFS2_SB(inode->i_sb), lockres, level, 0,
				    0);
	if (status < 0)
		mlog_errno(status);

	mlog_exit(status);
	return status;
}

void ocfs2_rw_unlock(struct inode *inode, int write)
{
	int level = write ? DLM_LOCK_EX : DLM_LOCK_PR;
	struct ocfs2_lock_res *lockres = &OCFS2_I(inode)->ip_rw_lockres;
	struct ocfs2_super *osb = OCFS2_SB(inode->i_sb);

	mlog_entry_void();

	mlog(0, "inode %llu drop %s RW lock\n",
	     (unsigned long long)OCFS2_I(inode)->ip_blkno,
	     write ? "EXMODE" : "PRMODE");

	if (!ocfs2_mount_local(osb))
		ocfs2_cluster_unlock(OCFS2_SB(inode->i_sb), lockres, level);

	mlog_exit_void();
}

/*
 * ocfs2_open_lock always get PR mode lock.
 */
int ocfs2_open_lock(struct inode *inode)
{
	int status = 0;
	struct ocfs2_lock_res *lockres;
	struct ocfs2_super *osb = OCFS2_SB(inode->i_sb);

	BUG_ON(!inode);

	mlog_entry_void();

	mlog(0, "inode %llu take PRMODE open lock\n",
	     (unsigned long long)OCFS2_I(inode)->ip_blkno);

	if (ocfs2_mount_local(osb))
		goto out;

	lockres = &OCFS2_I(inode)->ip_open_lockres;

	status = ocfs2_cluster_lock(OCFS2_SB(inode->i_sb), lockres,
				    DLM_LOCK_PR, 0, 0);
	if (status < 0)
		mlog_errno(status);

out:
	mlog_exit(status);
	return status;
}

int ocfs2_try_open_lock(struct inode *inode, int write)
{
	int status = 0, level;
	struct ocfs2_lock_res *lockres;
	struct ocfs2_super *osb = OCFS2_SB(inode->i_sb);

	BUG_ON(!inode);

	mlog_entry_void();

	mlog(0, "inode %llu try to take %s open lock\n",
	     (unsigned long long)OCFS2_I(inode)->ip_blkno,
	     write ? "EXMODE" : "PRMODE");

	if (ocfs2_mount_local(osb))
		goto out;

	lockres = &OCFS2_I(inode)->ip_open_lockres;

	level = write ? DLM_LOCK_EX : DLM_LOCK_PR;

	/*
	 * The file system may already holding a PRMODE/EXMODE open lock.
	 * Since we pass DLM_LKF_NOQUEUE, the request won't block waiting on
	 * other nodes and the -EAGAIN will indicate to the caller that
	 * this inode is still in use.
	 */
	status = ocfs2_cluster_lock(OCFS2_SB(inode->i_sb), lockres,
				    level, DLM_LKF_NOQUEUE, 0);

out:
	mlog_exit(status);
	return status;
}

/*
 * ocfs2_open_unlock unlock PR and EX mode open locks.
 