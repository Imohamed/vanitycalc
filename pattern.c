/*
 * Vanitygen, vanity bitcoin address generator
 * Copyright (C) 2011 <samr7@cs.washington.edu>
 *
 * Vanitygen is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version. 
 *
 * Vanitygen is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with Vanitygen.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <Python.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include <pthread.h>

#include <openssl/sha.h>
#include <openssl/ripemd.h>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/obj_mac.h>

#include <pcre.h>

#include "pattern.h"
#include "avl.h"

const signed char vg_b58_reverse_map[256] = {
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1,  0,  1,  2,  3,  4,  5,  6,  7,  8, -1, -1, -1, -1, -1, -1,
	-1,  9, 10, 11, 12, 13, 14, 15, 16, -1, 17, 18, 19, 20, 21, -1,
	22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, -1, -1, -1, -1, -1,
	-1, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, -1, 44, 45, 46,
	47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1
};


void
vg_context_free(vg_context_t *vcp)
{
	//vg_timing_info_free(vcp);
	vcp->vc_free(vcp);
}

double
vg_context_add_patterns(vg_context_t *vcp,
			PyObject *patterns)
{
	vcp->vc_pattern_generation++;
	return vcp->vc_add_patterns(vcp, patterns);
}

void
vg_context_clear_all_patterns(vg_context_t *vcp)
{
	vcp->vc_clear_all_patterns(vcp);
	vcp->vc_pattern_generation++;
}

int
vg_context_hash160_sort(vg_context_t *vcp, void *buf)
{
	if (!vcp->vc_hash160_sort)
		return 0;
	return vcp->vc_hash160_sort(vcp, buf);
}

/*
 * Find the bignum ranges that produce a given prefix.
 */
static int
get_prefix_ranges(int addrtype, const char *pfx, BIGNUM **result,
		  BN_CTX *bnctx)
{
	int i, p, c;
	int zero_prefix = 0;
	int check_upper = 0;
	int b58pow, b58ceil, b58top = 0;
	int ret = -1;

	BIGNUM bntarg, bnceil, bnfloor;
	BIGNUM bnbase;
	BIGNUM *bnap, *bnbp, *bntp;
	BIGNUM *bnhigh = NULL, *bnlow = NULL, *bnhigh2 = NULL, *bnlow2 = NULL;
	BIGNUM bntmp, bntmp2;

	BN_init(&bntarg);
	BN_init(&bnceil);
	BN_init(&bnfloor);
	BN_init(&bnbase);
	BN_init(&bntmp);
	BN_init(&bntmp2);

	BN_set_word(&bnbase, 58);

	p = strlen(pfx);

	for (i = 0; i < p; i++) {
		c = vg_b58_reverse_map[(int)pfx[i]];
		if (c == -1) {
			goto out;
		}
		if (i == zero_prefix) {
			if (c == 0) {
				/* Add another zero prefix */
				zero_prefix++;
				if (zero_prefix > 19) {
					goto out;
				}
				continue;
			}

			/* First non-zero character */
			b58top = c;
			BN_set_word(&bntarg, c);

		} else {
			BN_set_word(&bntmp2, c);
			BN_mul(&bntmp, &bntarg, &bnbase, bnctx);
			BN_add(&bntarg, &bntmp, &bntmp2);
		}
	}

	/* Power-of-two ceiling and floor values based on leading 1s */
	BN_clear(&bntmp);
	BN_set_bit(&bntmp, 200 - (zero_prefix * 8));
	BN_sub(&bnceil, &bntmp, BN_value_one());
	BN_set_bit(&bnfloor, 192 - (zero_prefix * 8));

	bnlow = BN_new();
	bnhigh = BN_new();

	if (b58top) {
		/*
		 * If a non-zero was given in the prefix, find the
		 * numeric boundaries of the prefix.
		 */

		BN_copy(&bntmp, &bnceil);
		bnap = &bntmp;
		bnbp = &bntmp2;
		b58pow = 0;
		while (BN_cmp(bnap, &bnbase) > 0) {
			b58pow++;
			BN_div(bnbp, NULL, bnap, &bnbase, bnctx);
			bntp = bnap;
			bnap = bnbp;
			bnbp = bntp;
		}
		b58ceil = BN_get_word(bnap);

		if ((b58pow - (p - zero_prefix)) < 6) {
			/*
			 * Do not allow the prefix to constrain the
			 * check value, this is ridiculous.
			 */
			fprintf(stderr, "Prefix '%s' is too long\n", pfx);
			goto out;
		}

		BN_set_word(&bntmp2, b58pow - (p - zero_prefix));
		BN_exp(&bntmp, &bnbase, &bntmp2, bnctx);
		BN_mul(bnlow, &bntmp, &bntarg, bnctx);
		BN_sub(&bntmp2, &bntmp, BN_value_one());
		BN_add(bnhigh, bnlow, &bntmp2);

		if (b58top <= b58ceil) {
			/* Fill out the upper range too */
			check_upper = 1;
			bnlow2 = BN_new();
			bnhigh2 = BN_new();

			BN_mul(bnlow2, bnlow, &bnbase, bnctx);
			BN_mul(&bntmp2, bnhigh, &bnbase, bnctx);
			BN_set_word(&bntmp, 57);
			BN_add(bnhigh2, &bntmp2, &bntmp);

			/*
			 * Addresses above the ceiling will have one
			 * fewer "1" prefix in front than we require.
			 */
			if (BN_cmp(&bnceil, bnlow2) < 0) {
				/* High prefix is above the ceiling */
				check_upper = 0;
				BN_free(bnhigh2);
				bnhigh2 = NULL;
				BN_free(bnlow2);
				bnlow2 = NULL;
			}
			else if (BN_cmp(&bnceil, bnhigh2) < 0)
				/* High prefix is partly above the ceiling */
				BN_copy(bnhigh2, &bnceil);

			/*
			 * Addresses below the floor will have another
			 * "1" prefix in front instead of our target.
			 */
			if (BN_cmp(&bnfloor, bnhigh) >= 0) {
				/* Low prefix is completely below the floor */
				assert(check_upper);
				check_upper = 0;
				BN_free(bnhigh);
				bnhigh = bnhigh2;
				bnhigh2 = NULL;
				BN_free(bnlow);
				bnlow = bnlow2;
				bnlow2 = NULL;
			}			
			else if (BN_cmp(&bnfloor, bnlow) > 0) {
				/* Low prefix is partly below the floor */
				BN_copy(bnlow, &bnfloor);
			}
		}

	} else {
		BN_copy(bnhigh, &bnceil);
		BN_clear(bnlow);
	}

	/* Limit the prefix to the address type */
	BN_clear(&bntmp);
	BN_set_word(&bntmp, addrtype);
	BN_lshift(&bntmp2, &bntmp, 192);

	if (check_upper) {
		if (BN_cmp(&bntmp2, bnhigh2) > 0) {
			check_upper = 0;
			BN_free(bnhigh2);
			bnhigh2 = NULL;
			BN_free(bnlow2);
			bnlow2 = NULL;
		}
		else if (BN_cmp(&bntmp2, bnlow2) > 0)
			BN_copy(bnlow2, &bntmp2);
	}

	if (BN_cmp(&bntmp2, bnhigh) > 0) {
		if (!check_upper)
			goto not_possible;
		check_upper = 0;
		BN_free(bnhigh);
		bnhigh = bnhigh2;
		bnhigh2 = NULL;
		BN_free(bnlow);
		bnlow = bnlow2;
		bnlow2 = NULL;
	}
	else if (BN_cmp(&bntmp2, bnlow) > 0) {
		BN_copy(bnlow, &bntmp2);
	}

	BN_set_word(&bntmp, addrtype + 1);
	BN_lshift(&bntmp2, &bntmp, 192);

	if (check_upper) {
		if (BN_cmp(&bntmp2, bnlow2) < 0) {
			check_upper = 0;
			BN_free(bnhigh2);
			bnhigh2 = NULL;
			BN_free(bnlow2);
			bnlow2 = NULL;
		}
		else if (BN_cmp(&bntmp2, bnhigh2) < 0)
			BN_copy(bnlow2, &bntmp2);
	}

	if (BN_cmp(&bntmp2, bnlow) < 0) {
		if (!check_upper)
			goto not_possible;
		check_upper = 0;
		BN_free(bnhigh);
		bnhigh = bnhigh2;
		bnhigh2 = NULL;
		BN_free(bnlow);
		bnlow = bnlow2;
		bnlow2 = NULL;
	}
	else if (BN_cmp(&bntmp2, bnhigh) < 0) {
		BN_copy(bnhigh, &bntmp2);
	}

	/* Address ranges are complete */
	assert(check_upper || ((bnlow2 == NULL) && (bnhigh2 == NULL)));
	result[0] = bnlow;
	result[1] = bnhigh;
	result[2] = bnlow2;
	result[3] = bnhigh2;
	bnlow = NULL;
	bnhigh = NULL;
	bnlow2 = NULL;
	bnhigh2 = NULL;
	ret = 0;

	if (0) {
	not_possible:
		ret = -2;
	}

out:
	BN_clear_free(&bntarg);
	BN_clear_free(&bnceil);
	BN_clear_free(&bnfloor);
	BN_clear_free(&bnbase);
	BN_clear_free(&bntmp);
	BN_clear_free(&bntmp2);
	if (bnhigh)
		BN_free(bnhigh);
	if (bnlow)
		BN_free(bnlow);
	if (bnhigh2)
		BN_free(bnhigh2);
	if (bnlow2)
		BN_free(bnlow2);

	return ret;
}

/*
 * Address prefix AVL tree node
 */

const int vpk_nwords = (25 + sizeof(BN_ULONG) - 1) / sizeof(BN_ULONG);

typedef struct _vg_prefix_s {
	avl_item_t		vp_item;
	struct _vg_prefix_s	*vp_sibling;
	const char		*vp_pattern;
	BIGNUM			*vp_low;
	BIGNUM			*vp_high;
} vg_prefix_t;

static void
vg_prefix_free(vg_prefix_t *vp)
{
	if (vp->vp_low)
		BN_free(vp->vp_low);
	if (vp->vp_high)
		BN_free(vp->vp_high);
	free(vp);
}

static vg_prefix_t *
vg_prefix_avl_insert(avl_root_t *rootp, vg_prefix_t *vpnew)
{
	vg_prefix_t *vp;
	avl_item_t *itemp = NULL;
	avl_item_t **ptrp = &rootp->ar_root;
	while (*ptrp) {
		itemp = *ptrp;
		vp = avl_item_entry(itemp, vg_prefix_t, vp_item);
		if (BN_cmp(vp->vp_low, vpnew->vp_high) > 0) {
			ptrp = &itemp->ai_left;
		} else {
			if (BN_cmp(vp->vp_high, vpnew->vp_low) < 0) {
				ptrp = &itemp->ai_right;
			} else
				return vp;
		}
	}
	vpnew->vp_item.ai_up = itemp;
	itemp = &vpnew->vp_item;
	*ptrp = itemp;
	avl_insert_fix(rootp, itemp);
	return NULL;
}

static vg_prefix_t *
vg_prefix_add(avl_root_t *rootp, const char *pattern, BIGNUM *low, BIGNUM *high)
{
	vg_prefix_t *vp, *vp2;
	assert(BN_cmp(low, high) < 0);
	vp = (vg_prefix_t *) malloc(sizeof(*vp));
	if (vp) {
		avl_item_init(&vp->vp_item);
		vp->vp_sibling = NULL;
		vp->vp_pattern = pattern;
		vp->vp_low = low;
		vp->vp_high = high;
		vp2 = vg_prefix_avl_insert(rootp, vp);
		if (vp2 != NULL) {
			fprintf(stderr,
				"Prefix '%s' ignored, overlaps '%s'\n",
				pattern, vp2->vp_pattern);
			vg_prefix_free(vp);
			vp = NULL;
		}
	}
	return vp;
}

static void
vg_prefix_delete(avl_root_t *rootp, vg_prefix_t *vp)
{
	vg_prefix_t *sibp, *delp;

	avl_remove(rootp, &vp->vp_item);
	sibp = vp->vp_sibling;
	while (sibp && sibp != vp) {
		avl_remove(rootp, &sibp->vp_item);
		delp = sibp;
		sibp = sibp->vp_sibling;
		vg_prefix_free(delp);
	}
	vg_prefix_free(vp);
}

static vg_prefix_t *
vg_prefix_add_ranges(avl_root_t *rootp, const char *pattern, BIGNUM **ranges,
		     vg_prefix_t *master)
{
	vg_prefix_t *vp, *vp2 = NULL;

	assert(ranges[0]);
	vp = vg_prefix_add(rootp, pattern, ranges[0], ranges[1]);
	if (!vp)
		return NULL;

	if (ranges[2]) {
		vp2 = vg_prefix_add(rootp, pattern, ranges[2], ranges[3]);
		if (!vp2) {
			vg_prefix_delete(rootp, vp);
			return NULL;
		}
	}

	if (!master) {
		vp->vp_sibling = vp2;
		if (vp2)
			vp2->vp_sibling = vp;
	} else if (vp2) {
		vp->vp_sibling = vp2;
		vp2->vp_sibling = (master->vp_sibling ? 
				   master->vp_sibling :
				   master);
		master->vp_sibling = vp;
	} else {
		vp->vp_sibling = (master->vp_sibling ? 
				  master->vp_sibling :
				  master);
		master->vp_sibling = vp;
	}
	return vp;
}

static void
vg_prefix_range_sum(vg_prefix_t *vp, BIGNUM *result, BIGNUM *tmp1)
{
	vg_prefix_t *startp;

	startp = vp;
	BN_clear(result);
	do {
		BN_sub(tmp1, vp->vp_high, vp->vp_low);
		BN_add(result, result, tmp1);
		vp = vp->vp_sibling;
	} while (vp && (vp != startp));
}


typedef struct _prefix_case_iter_s {
	char	ci_prefix[32];
	char	ci_case_map[32];
	char	ci_nbits;
	int	ci_value;
} prefix_case_iter_t;

static const unsigned char b58_case_map[256] = {
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 0, 1, 1, 2,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
	0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 2, 1, 1, 0,
	1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0,
};

static int
prefix_case_iter_init(prefix_case_iter_t *cip, const char *pfx)
{
	int i;

	cip->ci_nbits = 0;
	cip->ci_value = 0;
	for (i = 0; pfx[i]; i++) {
		if (i > sizeof(cip->ci_prefix))
			return 0;
		if (!b58_case_map[(int)pfx[i]]) {
			/* Character isn't case-swappable, ignore it */
			cip->ci_prefix[i] = pfx[i];
			continue;
		}
		if (b58_case_map[(int)pfx[i]] == 2) {
			/* Character invalid, but valid in swapped case */
			cip->ci_prefix[i] = pfx[i] ^ 0x20;
			continue;
		}
		/* Character is case-swappable */
		cip->ci_prefix[i] = pfx[i] | 0x20;
		cip->ci_case_map[(int)cip->ci_nbits] = i;
		cip->ci_nbits++;
	}
	cip->ci_prefix[i] = '\0';
	return 1;
}

static int
prefix_case_iter_next(prefix_case_iter_t *cip)
{
	unsigned long val, max, mask;
	int i, nbits;

	nbits = cip->ci_nbits;
	max = (1UL << nbits) - 1;
	val = cip->ci_value + 1;
	if (val > max)
		return 0;

	for (i = 0, mask = 1; i < nbits; i++, mask <<= 1) {
		if (val & mask)
			cip->ci_prefix[(int)cip->ci_case_map[i]] &= 0xdf;
		else
			cip->ci_prefix[(int)cip->ci_case_map[i]] |= 0x20;
	}
	cip->ci_value = val;
	return 1;
}


typedef struct _vg_prefix_context_s {
	vg_context_t		base;
	avl_root_t		vcp_avlroot;
	BIGNUM			vcp_difficulty;
	int			vcp_caseinsensitive;
} vg_prefix_context_t;

void
vg_prefix_context_set_case_insensitive(vg_context_t *vcp, int caseinsensitive)
{
	((vg_prefix_context_t *) vcp)->vcp_caseinsensitive = caseinsensitive;
}

static void
vg_prefix_context_clear_all_patterns(vg_context_t *vcp)
{
	vg_prefix_context_t *vcpp = (vg_prefix_context_t *) vcp;
	vg_prefix_t *vp;
	unsigned long npfx_left = 0;

	while (!avl_root_empty(&vcpp->vcp_avlroot)) {
		vp = avl_item_entry(vcpp->vcp_avlroot.ar_root,
				    vg_prefix_t, vp_item);
		vg_prefix_delete(&vcpp->vcp_avlroot, vp);
		npfx_left++;
	}

	assert(npfx_left == vcpp->base.vc_npatterns);
	vcpp->base.vc_npatterns = 0;
	vcpp->base.vc_npatterns_start = 0;
	vcpp->base.vc_found = 0;
	BN_clear(&vcpp->vcp_difficulty);
}

static void
vg_prefix_context_free(vg_context_t *vcp)
{
	vg_prefix_context_t *vcpp = (vg_prefix_context_t *) vcp;
	vg_prefix_context_clear_all_patterns(vcp);
	BN_clear_free(&vcpp->vcp_difficulty);
	free(vcpp);
}

static double
vg_prefix_context_next_difficulty(vg_prefix_context_t *vcpp,
				  BIGNUM *bntmp, BIGNUM *bntmp2, BN_CTX *bnctx)
{
	double diff;
	char *dbuf;
	
	BN_clear(bntmp);
	BN_set_bit(bntmp, 192);
	BN_div(bntmp2, NULL, bntmp, &vcpp->vcp_difficulty, bnctx);
	dbuf = BN_bn2dec(bntmp2);
	diff = atof(dbuf);
	OPENSSL_free(dbuf);
	
	return diff;
}

static double
vg_prefix_context_add_patterns(vg_context_t *vcp, PyObject *patterns)
{
	vg_prefix_context_t *vcpp = (vg_prefix_context_t *) vcp;
	prefix_case_iter_t caseiter;
	vg_prefix_t *vp, *vp2;
	BN_CTX *bnctx;
	BIGNUM bntmp, bntmp2, bntmp3;
	BIGNUM *ranges[4];
	double ret = 0;
	int i, impossible = 0;
	int case_impossible;
	unsigned long npfx;
	char *pattern;

	bnctx = BN_CTX_new();
	BN_init(&bntmp);
	BN_init(&bntmp2);
	BN_init(&bntmp3);

	npfx = 0;
	for (i = 0; i < PyList_Size(patterns); i++) {
		pattern = PyString_AsString(PyList_GetItem(patterns, i));
		if (!vcpp->vcp_caseinsensitive) {
			vp = NULL;
			ret = get_prefix_ranges(vcpp->base.vc_addrtype,
						pattern,
						ranges, bnctx);
			if (!ret) {
				vp = vg_prefix_add_ranges(&vcpp->vcp_avlroot,
							  pattern,
							  ranges, NULL);
			}

		} else {
			/* Case-enumerate the prefix */
			if (!prefix_case_iter_init(&caseiter, pattern)) {
				continue;
			}

			case_impossible = 0;
			vp = NULL;
			do {
				ret = get_prefix_ranges(vcpp->base.vc_addrtype,
							caseiter.ci_prefix,
							ranges, bnctx);
				if (ret == -2) {
					case_impossible++;
					ret = 0;
					continue;
				}
				if (ret)
					break;
				vp2 = vg_prefix_add_ranges(&vcpp->vcp_avlroot,
							   pattern,
							   ranges,
							   vp);
				if (!vp2) {
					ret = -1;
					break;
				}
				if (!vp)
					vp = vp2;

			} while (prefix_case_iter_next(&caseiter));

			if (!vp && case_impossible)
				ret = -2;

			if (ret && vp) {
				vg_prefix_delete(&vcpp->vcp_avlroot, vp);
				vp = NULL;
			}
		}

		if (ret == -2) {
			impossible++;
		}

		if (!vp)
			continue;

		npfx++;

		/* Determine the probability of finding a match */
		vg_prefix_range_sum(vp, &bntmp, &bntmp2);
		BN_add(&bntmp2, &vcpp->vcp_difficulty, &bntmp);
		BN_copy(&vcpp->vcp_difficulty, &bntmp2);
	}

	ret = vg_prefix_context_next_difficulty(vcpp, &bntmp, &bntmp2, bnctx);

	BN_clear_free(&bntmp);
	BN_clear_free(&bntmp2);
	BN_clear_free(&bntmp3);
	BN_CTX_free(bnctx);
	
	return ret;
}

vg_context_t *
vg_prefix_context_new(int addrtype, int privtype, int caseinsensitive)
{
	vg_prefix_context_t *vcpp;

	vcpp = (vg_prefix_context_t *) malloc(sizeof(*vcpp));
	if (vcpp) {
		memset(vcpp, 0, sizeof(*vcpp));
		vcpp->base.vc_addrtype = addrtype;
		vcpp->base.vc_privtype = privtype;
		vcpp->base.vc_npatterns = 0;
		vcpp->base.vc_npatterns_start = 0;
		vcpp->base.vc_found = 0;
		vcpp->base.vc_chance = 0.0;
		vcpp->base.vc_free = vg_prefix_context_free;
		vcpp->base.vc_add_patterns = vg_prefix_context_add_patterns;
		vcpp->base.vc_clear_all_patterns =
			vg_prefix_context_clear_all_patterns;

		avl_root_init(&vcpp->vcp_avlroot);
		BN_init(&vcpp->vcp_difficulty);
		vcpp->vcp_caseinsensitive = caseinsensitive;
	}
	return &vcpp->base;
}

