#include <stdio.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include <pthread.h>

#include <openssl/sha.h>
#include <openssl/ripemd.h>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/obj_mac.h>


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
			fprintf(stderr,
				"Invalid character '%c' in prefix '%s'\n",
				pfx[i], pfx);
			goto out;
		}
		if (i == zero_prefix) {
			if (c == 0) {
				/* Add another zero prefix */
				zero_prefix++;
				if (zero_prefix > 19) {
					fprintf(stderr,
						"Prefix '%s' is too long\n",
						pfx);
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

static void
free_ranges(BIGNUM **ranges)
{
	BN_free(ranges[0]);
	BN_free(ranges[1]);
	ranges[0] = NULL;
	ranges[1] = NULL;
	if (ranges[2]) {
		BN_free(ranges[2]);
		BN_free(ranges[3]);
		ranges[2] = NULL;
		ranges[3] = NULL;
	}
}


double
vg_prefix_get_difficulty(int addrtype, const char *pattern)
{
	BN_CTX *bnctx;
	BIGNUM result, bntmp;
	BIGNUM *ranges[4];
	char *dbuf;
	int ret;
	double diffret = 0.0;

	bnctx = BN_CTX_new();
	BN_init(&result);
	BN_init(&bntmp);

	ret = get_prefix_ranges(addrtype, pattern, ranges, bnctx);

	if (ret == 0) {
		BN_sub(&bntmp, ranges[1], ranges[0]);
		BN_add(&result, &result, &bntmp);
		if (ranges[2]) {
			BN_sub(&bntmp, ranges[3], ranges[2]);
			BN_add(&result, &result, &bntmp);
		}
		free_ranges(ranges);

		BN_clear(&bntmp);
		BN_set_bit(&bntmp, 192);
		BN_div(&result, NULL, &bntmp, &result, bnctx);

		dbuf = BN_bn2dec(&result);
		diffret = strtod(dbuf, NULL);
		OPENSSL_free(dbuf);
	}

	BN_clear_free(&result);
	BN_clear_free(&bntmp);
	BN_CTX_free(bnctx);
	return diffret;
}

int
main(int argc, char **argv)
{
	printf("Difficulty: %lld\n", (long long int)vg_prefix_get_difficulty(0, argv[1]));
}
