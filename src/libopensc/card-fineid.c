/*
 * card-fineid.c: Support for FINeID v3 (Oberthur) smart cards.
 *
 * Oberthur
 * Copyright (C) 2001, 2002  Juha Yrjölä <juha.yrjola@iki.fi>
 * Copyright (C) 2009  Viktor Tarasov <viktor.tarasov@opentrust.com>,
 *                     OpenTrust <www.opentrust.com>
 *
 * FINeID v3
 * Copyright (C) 2019  Juho Tykkälä <juho.tykkala@phnet.fi>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * best view with tabstop=4
 */

#if HAVE_CONFIG_H
#include "config.h"
#endif

#ifdef ENABLE_OPENSSL
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <openssl/sha.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/opensslv.h>

#include "internal.h"
#include "cardctl.h"
#include "pkcs15.h"
#include "iso7816.h"
#include "types.h"

#define FINEID_PIN_LOCAL             0x80
#define FINEID_PIN_REFERENCE_USER    0x81
#define FINEID_PIN_REFERENCE_ONETIME 0x82
#define FINEID_PIN_REFERENCE_SO      0x04
#define FINEID_PIN_REFERENCE_PUK     0x84

#define FINEID_ALGO_HIGH_NA     0x00
#define FINEID_ALGO_HIGH_SHA1   0x10
#define FINEID_ALGO_HIGH_SHA224 0x30
#define FINEID_ALGO_HIGH_SHA256 0x40
#define FINEID_ALGO_HIGH_SHA384 0x50
#define FINEID_ALGO_HIGH_SHA512 0x60

#define FINEID_ALGO_LOW_NA           0x00
#define FINEID_ALGO_LOW_RSA_9796     0x01
#define FINEID_ALGO_LOW_RSASSA_PKCS1 0x02
#define FINEID_ALGO_LOW_RSA_2409     0x03
#define FINEID_ALGO_LOW_ECDSA        0x04
#define FINEID_ALGO_LOW_RSA_PSS      0x05

#define FINEID_CT_RSASSA_PKCS1      0x1A
#define FINEID_CT_RSAES_OAEP_SHA1   0x1D
#define FINEID_CT_RSAES_OAEP_SHA224 0x3D
#define FINEID_CT_RSAES_OAEP_SHA256 0x4D
#define FINEID_CT_RSAES_OAEP_SHA384 0x5D
#define FINEID_CT_RSAES_OAEP_SHA512 0x6D

#define FINEID_HASHING_BY_CARD    0x80
#define FINEID_HASHING_EXTERNALLY 0x90

static const struct sc_atr_table fineid_atrs[] = {
	{ "3B:7F:96:00:00:80:31:B8:65:B0:85:03:00:EF:12:00:F6:82:90:00",
		NULL, "FINeID v3", SC_CARD_TYPE_OBERTHUR_FINEID_3, 0, NULL },
	{ NULL, NULL, NULL, 0, 0, NULL }
};

struct private_driver_data {
	unsigned char aid[SC_MAX_AID_SIZE], key_ref_msb;
	int           aid_len, operation;
	unsigned int  algorithm, algorithm_flags;
	long int      sn;
};

static const unsigned char *aid_FINEID =
	(const unsigned char *)"\xA0\x00\x00\x00\x63\x50\x4B\x43\x53\x2D\x31\x35";

static const int lenAid_FINEID = 12;
static const char *nameAid_FINEID = "FINeID v3";

static const struct sc_aid fineid_cm_aid = {
	{0xA0, 0x00, 0x00, 0x00, 0x63, 0x50, 0x4B, 0x43, 0x53, 0x2D, 0x31, 0x35}, 12
};

#define FINEID_AUTH_TYPE_PIN 1
#define FINEID_AUTH_MAX_LENGTH_PIN 12

#define SC_FINEID_MAX_ATTR_SIZE 8

#define PUBKEY_512_ASN1_SIZE  0x4A
#define PUBKEY_1024_ASN1_SIZE 0x8C
#define PUBKEY_2048_ASN1_SIZE 0x10E

static struct sc_file *auth_current_ef = NULL, *auth_current_df = NULL;
static struct sc_card_operations auth_ops;
static struct sc_card_operations *iso_ops;
static struct sc_card_driver auth_drv = {
	"FINeID v3 (Oberthur)",
	"fineid",
	&auth_ops,
	NULL, 0, NULL
};

//static int auth_get_pin_reference (struct sc_card *card,
//	int type, int reference, int cmd, int *out_ref);
static int auth_get_serialnr(struct sc_card *card,
	struct sc_serial_number *serial);
static int auth_select_file(struct sc_card *card, const struct sc_path *in_path,
	struct sc_file **file_out);


static int
auth_finish(struct sc_card *card)
{
	free(card->drv_data);
	return SC_SUCCESS;
}


int
select_card_manager(struct sc_card *card, const struct sc_aid *aid)
{
	LOG_FUNC_CALLED(card->ctx);
	
	struct sc_apdu apdu;
	int rv;

	sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0xA4, 0x04, 0x0C);
	apdu.lc = aid->len;
	apdu.data = aid->value;
	apdu.datalen = aid->len;

	rv = sc_transmit_apdu(card, &apdu);

	if (rv < 0)
		return rv;

	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	if (rv < 0)
		return rv;

	LOG_FUNC_RETURN(card->ctx, apdu.resplen);
}


static int
auth_select_aid(struct sc_card *card)
{
	struct sc_apdu apdu;
	unsigned char apdu_resp[SC_MAX_APDU_BUFFER_SIZE];
	struct private_driver_data *_driver_data =  (struct private_driver_data *) card->drv_data;
	int rv, ii;
	struct sc_path tmp_path;

	/* Select Card Manager (to deselect previously selected application) */
	rv = select_card_manager(card, &fineid_cm_aid);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");

	/* Get smart card serial number */
	sc_format_apdu(card, &apdu, SC_APDU_CASE_2_SHORT, 0xCA, 0x9F, 0x7F);
	apdu.cla = 0x80;
	apdu.le = 0x2D;
	apdu.resplen = 0x30;
	apdu.resp = apdu_resp;

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	card->serialnr.len = 4;
	memcpy(card->serialnr.value, apdu.resp+15, 4);

	for (ii=0, _driver_data->sn = 0; ii < 4; ii++)
		_driver_data->sn += (long int)(*(apdu.resp + 15 + ii)) << (3-ii)*8;

	sc_log(card->ctx, "serial number %li/0x%lX", _driver_data->sn, _driver_data->sn);

	memset(&tmp_path, 0, sizeof(struct sc_path));
	tmp_path.type = SC_PATH_TYPE_DF_NAME;
	
	memcpy(tmp_path.value, aid_FINEID, lenAid_FINEID);
	tmp_path.len = lenAid_FINEID;

	rv = iso_ops->select_file(card, &tmp_path, NULL);
	LOG_TEST_RET(card->ctx, rv, "select parent failed");

	sc_format_path("3F002F00", &tmp_path);
	rv = iso_ops->select_file(card, &tmp_path, &auth_current_df);
	LOG_TEST_RET(card->ctx, rv, "select parent failed");

	sc_format_path("3F002F00", &card->cache.current_path);
	sc_file_dup(&auth_current_ef, auth_current_df);
	
	memcpy(_driver_data->aid, aid_FINEID, lenAid_FINEID);
	_driver_data->aid_len = lenAid_FINEID;
	card->name = nameAid_FINEID;

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_match_card(struct sc_card *card)
{
	if (_sc_match_atr(card, fineid_atrs, &card->type) < 0)
		return 0;
	else
		return 1;
}


static int
auth_init(struct sc_card *card)
{
	struct private_driver_data *_driver_data;
	struct sc_path path;
	unsigned long flags;
	int rv = 0;

	_driver_data = calloc(1, sizeof(struct private_driver_data));

	if (!_driver_data)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_OUT_OF_MEMORY);

	card->cla = 0x00;
	card->drv_data = _driver_data;

	card->caps |= SC_CARD_CAP_RNG;
	card->caps |= SC_CARD_CAP_USE_FCI_AC;

	if (auth_select_aid(card))   {
		sc_log(card->ctx, "Failed to initialize %s", card->name);
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_CARD, "Failed to initialize");
	}

	flags = SC_ALGORITHM_RSA_PAD_PKCS1;
	flags |= SC_ALGORITHM_RSA_HASH_SHA1;
	flags |= SC_ALGORITHM_RSA_HASH_SHA224;
	flags |= SC_ALGORITHM_RSA_HASH_SHA256;
	flags |= SC_ALGORITHM_RSA_HASH_SHA384;
	flags |= SC_ALGORITHM_RSA_HASH_SHA512;

	_sc_card_add_rsa_alg(card, 512, flags, 0);
	_sc_card_add_rsa_alg(card, 1024, flags, 0);
	_sc_card_add_rsa_alg(card, 2048, flags, 0);

	sc_format_path("3F00", &path);
	rv = auth_select_file(card, &path, NULL);

	LOG_FUNC_RETURN(card->ctx, rv);
}


static void
add_acl_entry(struct sc_card *card, struct sc_file *file, unsigned int op,
		unsigned char acl_byte)
{
	if ((acl_byte & 0xE0) == 0x60)   {
		sc_log(card->ctx, "called; op 0x%X; SC_AC_PRO; ref 0x%X", op, acl_byte);
		sc_file_add_acl_entry(file, op, SC_AC_PRO, acl_byte);
		return;
	}

	switch (acl_byte) {
	case 0x00:
		sc_file_add_acl_entry(file, op, SC_AC_NONE, SC_AC_KEY_REF_NONE);
		break;
	/* User and OneTime PINs are locals */
	case 0x21:
	case 0x22:
		sc_file_add_acl_entry(file, op, SC_AC_CHV, (acl_byte & 0x0F) | FINEID_PIN_LOCAL);
		break;
	/* Local SOPIN is only for the unblocking. */
	case 0x24:
	case 0x25:
		if (op == SC_AC_OP_PIN_RESET)
			sc_file_add_acl_entry(file, op, SC_AC_CHV, 0x84);
		else
			sc_file_add_acl_entry(file, op, SC_AC_CHV, 0x04);
		break;
	case 0xFF:
		sc_file_add_acl_entry(file, op, SC_AC_NEVER, SC_AC_KEY_REF_NONE);
		break;
	default:
		sc_file_add_acl_entry(file, op, SC_AC_UNKNOWN, SC_AC_KEY_REF_NONE);
		break;
	}
}


static int
tlv_get(struct sc_card *card, const unsigned char *msg, int len, unsigned char tag,
		unsigned char *ret, int *ret_len)
{
	int cur = 0;
	LOG_FUNC_CALLED(card->ctx);

	while (cur < len)  {
		if (*(msg+cur)==tag)  {
			int ii, ln = *(msg+cur+1);

			sc_log(card->ctx, "tag 0x%X found", tag);

			if (ln > *ret_len)
				LOG_FUNC_RETURN(card->ctx, SC_ERROR_WRONG_LENGTH);

			for (ii=0; ii<ln; ii++)
				*(ret + ii) = *(msg+cur+2+ii);
			*ret_len = ln;

			LOG_FUNC_RETURN(card->ctx, SC_SUCCESS);
		}

		cur += 2 + *(msg+cur+1);
	}

	sc_log(card->ctx, "tag 0x%X not present", tag);
	LOG_FUNC_RETURN(card->ctx, SC_ERROR_INCORRECT_PARAMETERS);
}


static int
auth_process_fci(struct sc_card *card, struct sc_file *file,
            const unsigned char *buf, size_t buflen)
{
	unsigned char type, attr[SC_FINEID_MAX_ATTR_SIZE];
	int attr_len = sizeof(attr);

	LOG_FUNC_CALLED(card->ctx);

	attr_len = sizeof(attr);
	if (tlv_get(card, buf, buflen, ISO7816_TAG_FCP_FID, attr, &attr_len))
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	file->id = attr[0]*0x100 + attr[1];

	sc_log(card->ctx, "assuming id 0x%X", file->id);

	// Skipping DF 5016 as not useful and will be
	// encountered only during path traversal
	if(file->id == 0x5016) {
		sc_log(card->ctx, "skipping 0x%X during path traversal", file->id);
		LOG_FUNC_RETURN(card->ctx, SC_SUCCESS);
	}

	attr_len = sizeof(attr);
	if (tlv_get(card, buf, buflen, ISO7816_TAG_FCP_TYPE, attr, &attr_len)) {
		type = ISO7816_FILE_TYPE_TRANSPARENT_EF; // FINeID default type
	} else {
		type = attr[0];
	}

	sc_log(card->ctx, "assuming type 0x%X", type);

	attr_len = sizeof(attr);
	if (tlv_get(card, buf, buflen, type==ISO7816_FILE_TYPE_TRANSPARENT_EF ? ISO7816_TAG_FCP_SIZE_FULL : ISO7816_TAG_FCP_PROP_INFO, attr, &attr_len))
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	if (attr_len<2 && type != 0x04)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);

	switch (type) {
	case 0x01:
		file->type = SC_FILE_TYPE_WORKING_EF;
		file->ef_structure = SC_FILE_EF_TRANSPARENT;
		file->size = attr[0]*0x100 + attr[1];
		break;
	case 0x04:
		file->type = SC_FILE_TYPE_WORKING_EF;
		file->ef_structure = SC_FILE_EF_LINEAR_VARIABLE;
		file->size = attr[0];
		attr_len = sizeof(attr);
		if (tlv_get(card, buf, buflen, 0x82, attr, &attr_len))
			LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
		if (attr_len!=5)
			LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
		file->record_length = attr[2]*0x100+attr[3];
		file->record_count = attr[4];
		break;
	case 0x12:
		file->type = SC_FILE_TYPE_INTERNAL_EF;
		file->ef_structure = SC_CARDCTL_OBERTHUR_KEY_RSA_PUBLIC;

		file->size = attr[0]*0x100 + attr[1];
		if (file->size==512)
			file->size = PUBKEY_512_ASN1_SIZE;
		else if (file->size==1024)
			file->size = PUBKEY_1024_ASN1_SIZE;
		else if (file->size==2048)
			file->size = PUBKEY_2048_ASN1_SIZE;
		else   {
			sc_log(card->ctx,
				   "Not supported public key size: %"SC_FORMAT_LEN_SIZE_T"u",
				   file->size);
			LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
		}
		break;
	case 0x14:
		file->type = SC_FILE_TYPE_INTERNAL_EF;
		file->ef_structure = SC_CARDCTL_OBERTHUR_KEY_RSA_CRT;
		file->size = attr[0]*0x100 + attr[1];
		break;
	case 0x38:
		file->type = SC_FILE_TYPE_DF;
		file->size = attr[0];
		if (SC_SUCCESS != sc_file_set_type_attr(file,attr,attr_len))
			LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
		break;
	default:
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	}

	// TODO: Implement the way ISO7816_TAG_FCP_ACLS is not needed as it is not present
	// Hard-coded for now, see reason bellow
	if (file->type == SC_FILE_TYPE_DF) {
		add_acl_entry(card, file, SC_AC_OP_SELECT, 0x00);
		add_acl_entry(card, file, SC_AC_OP_LOCK, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_DELETE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_CREATE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_REHABILITATE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_INVALIDATE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_LIST_FILES, 0xFF);
	} else {
		add_acl_entry(card, file, SC_AC_OP_WRITE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_UPDATE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_READ, 0x00);
		add_acl_entry(card, file, SC_AC_OP_ERASE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_REHABILITATE, 0xFF);
		add_acl_entry(card, file, SC_AC_OP_INVALIDATE, 0xFF);
	}
	
	// TODO: Tag ISO7816_TAG_FCP_ACLS not present in FINeID
	/*
	attr_len = sizeof(attr);
	if (tlv_get(card, buf, buflen, ISO7816_TAG_FCP_ACLS, attr, &attr_len))
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);
	if (attr_len<8)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_UNKNOWN_DATA_RECEIVED);

	if (file->type == SC_FILE_TYPE_DF) {
		add_acl_entry(card, file, SC_AC_OP_CREATE, attr[0]);
		add_acl_entry(card, file, SC_AC_OP_CRYPTO, attr[1]);
		add_acl_entry(card, file, SC_AC_OP_LIST_FILES, attr[2]);
		add_acl_entry(card, file, SC_AC_OP_DELETE, attr[3]);
		add_acl_entry(card, file, SC_AC_OP_PIN_DEFINE, attr[4]);
		add_acl_entry(card, file, SC_AC_OP_PIN_CHANGE, attr[5]);
		add_acl_entry(card, file, SC_AC_OP_PIN_RESET, attr[6]);
		sc_log(card->ctx, "SC_FILE_TYPE_DF:CRYPTO %X", attr[1]);
	}
	else if (file->type == SC_FILE_TYPE_INTERNAL_EF)  {
		switch (file->ef_structure) {
		case SC_CARDCTL_OBERTHUR_KEY_RSA_PUBLIC:
			add_acl_entry(card, file, SC_AC_OP_UPDATE, attr[0]);
			add_acl_entry(card, file, SC_AC_OP_PSO_ENCRYPT, attr[2]);
			add_acl_entry(card, file, SC_AC_OP_PSO_VERIFY_SIGNATURE, attr[4]);
			add_acl_entry(card, file, SC_AC_OP_EXTERNAL_AUTHENTICATE, attr[6]);
			break;
		case SC_CARDCTL_OBERTHUR_KEY_RSA_CRT:
			add_acl_entry(card, file, SC_AC_OP_UPDATE, attr[0]);
			add_acl_entry(card, file, SC_AC_OP_PSO_DECRYPT, attr[1]);
			add_acl_entry(card, file, SC_AC_OP_PSO_COMPUTE_SIGNATURE, attr[3]);
			add_acl_entry(card, file, SC_AC_OP_INTERNAL_AUTHENTICATE, attr[5]);
			break;
		}
	}
	else   {
		switch (file->ef_structure) {
		case SC_FILE_EF_TRANSPARENT:
			add_acl_entry(card, file, SC_AC_OP_WRITE, attr[0]);
			add_acl_entry(card, file, SC_AC_OP_UPDATE, attr[1]);
			add_acl_entry(card, file, SC_AC_OP_READ, attr[2]);
			add_acl_entry(card, file, SC_AC_OP_ERASE, attr[3]);
			break;
		case SC_FILE_EF_LINEAR_VARIABLE:
			add_acl_entry(card, file, SC_AC_OP_WRITE, attr[0]);
			add_acl_entry(card, file, SC_AC_OP_UPDATE, attr[1]);
			add_acl_entry(card, file, SC_AC_OP_READ, attr[2]);
			add_acl_entry(card, file, SC_AC_OP_ERASE, attr[3]);
			break;
		}
	}
	*/

	file->status = SC_FILE_STATUS_ACTIVATED;
	file->magic = SC_FILE_MAGIC;

	LOG_FUNC_RETURN(card->ctx, SC_SUCCESS);
}


static int
auth_select_file(struct sc_card *card, const struct sc_path *in_path,
				 struct sc_file **file_out)
{
	struct sc_path path;
	struct sc_file *tmp_file = NULL;
	size_t offs, ii;
	int rv;

	LOG_FUNC_CALLED(card->ctx);
	assert(card != NULL && in_path != NULL);

	memcpy(&path, in_path, sizeof(struct sc_path));

	if (!auth_current_df)
		return SC_ERROR_OBJECT_NOT_FOUND;

	sc_log(card->ctx, "in_path; type=%d, path=%s, out %p",
			in_path->type, sc_print_path(in_path), file_out);
	sc_log(card->ctx, "current path; type=%d, path=%s",
			auth_current_df->path.type, sc_print_path(&auth_current_df->path));
	if (auth_current_ef)
		sc_log(card->ctx, "current file; type=%d, path=%s",
				auth_current_ef->path.type, sc_print_path(&auth_current_ef->path));

	if (path.type == SC_PATH_TYPE_FILE_ID)   {
		sc_file_free(auth_current_ef);
		auth_current_ef = NULL;

		rv = iso_ops->select_file(card, &path, &tmp_file);
		LOG_TEST_RET(card->ctx, rv, "select file failed");
		if (!tmp_file)
			return SC_ERROR_OBJECT_NOT_FOUND;

		if (path.type == SC_PATH_TYPE_PARENT)   {
			memcpy(&tmp_file->path, &auth_current_df->path, sizeof(struct sc_path));
			if (tmp_file->path.len > 2)
				tmp_file->path.len -= 2;

			sc_file_free(auth_current_df);
			sc_file_dup(&auth_current_df, tmp_file);
		}
		else   {
			if (tmp_file->type == SC_FILE_TYPE_DF)   {
				sc_concatenate_path(&tmp_file->path, &auth_current_df->path, &path);

				sc_file_free(auth_current_df);
				sc_file_dup(&auth_current_df, tmp_file);
			}
			else   {
				sc_file_free(auth_current_ef);

				sc_file_dup(&auth_current_ef, tmp_file);
				sc_concatenate_path(&auth_current_ef->path, &auth_current_df->path, &path);
			}
		}
		if (file_out)
			sc_file_dup(file_out, tmp_file);

		sc_file_free(tmp_file);
	}
	else if (path.type == SC_PATH_TYPE_DF_NAME)   {
		rv = iso_ops->select_file(card, &path, NULL);
		if (rv)   {
			sc_file_free(auth_current_ef);
			auth_current_ef = NULL;
		}
		LOG_TEST_RET(card->ctx, rv, "select file failed");
	}
	else   {
		for (offs = 0; offs < path.len && offs < auth_current_df->path.len; offs += 2)
			if (path.value[offs] != auth_current_df->path.value[offs] ||
					path.value[offs + 1] != auth_current_df->path.value[offs + 1])
				break;

		sc_log(card->ctx, "offs %"SC_FORMAT_LEN_SIZE_T"u", offs);
		if (offs && offs < auth_current_df->path.len)   {
			size_t deep = auth_current_df->path.len - offs;

			sc_log(card->ctx, "deep %"SC_FORMAT_LEN_SIZE_T"u",
			       deep);
			for (ii=0; ii<deep; ii+=2)   {
				struct sc_path tmp_path;

				memcpy(&tmp_path, &auth_current_df->path,  sizeof(struct sc_path));
				tmp_path.type = SC_PATH_TYPE_PARENT;

				rv = auth_select_file (card, &tmp_path, file_out);
				LOG_TEST_RET(card->ctx, rv, "select file failed");
			}
		}

		if (path.len - offs > 0)   {
			struct sc_path tmp_path;

			memset(&tmp_path, 0, sizeof(struct sc_path));
			tmp_path.type = SC_PATH_TYPE_FILE_ID;
			tmp_path.len = 2;

			for (ii=0; ii < path.len - offs; ii+=2)   {
				memcpy(tmp_path.value, path.value + offs + ii, 2);

				sc_log(card->ctx, "iteration %lu begin", ii/2);
				rv = auth_select_file(card, &tmp_path, file_out);
				LOG_TEST_RET(card->ctx, rv, "select file failed");
				sc_log(card->ctx, "iteration %lu end", ii/2);
			}
		}
		else if (path.len - offs == 0 && file_out)  {
			if (sc_compare_path(&path, &auth_current_df->path))
				sc_file_dup(file_out, auth_current_df);
			else  if (auth_current_ef)
				sc_file_dup(file_out, auth_current_ef);
			else
				LOG_TEST_RET(card->ctx, SC_ERROR_INTERNAL, "No current EF");
		}
	}

	LOG_FUNC_RETURN(card->ctx, 0);
}


static int
auth_list_files(struct sc_card *card, unsigned char *buf, size_t buflen)
{
	struct sc_apdu apdu;
	unsigned char rbuf[SC_MAX_APDU_BUFFER_SIZE];
	int rv;

	LOG_FUNC_CALLED(card->ctx);
	sc_format_apdu(card, &apdu, SC_APDU_CASE_2_SHORT, 0x34, 0, 0);
	apdu.cla = 0x80;
	apdu.le = 0x40;
	apdu.resplen = sizeof(rbuf);
	apdu.resp = rbuf;

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");

	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Card returned error");

	if (apdu.resplen == 0x100 && rbuf[0]==0 && rbuf[1]==0)
		LOG_FUNC_RETURN(card->ctx, 0);

	buflen = buflen < apdu.resplen ? buflen : apdu.resplen;
	memcpy(buf, rbuf, buflen);

	LOG_FUNC_RETURN(card->ctx, buflen);
}


static unsigned int
auth_get_algo(unsigned int algorithm_flags)
{
	if (algorithm_flags & SC_ALGORITHM_RSA_HASH_SHA1)
		return FINEID_ALGO_HIGH_SHA1;
	else if (algorithm_flags & SC_ALGORITHM_RSA_HASH_SHA224)
		return FINEID_ALGO_HIGH_SHA224;
	else if (algorithm_flags & SC_ALGORITHM_RSA_HASH_SHA256)
		return FINEID_ALGO_HIGH_SHA256;
	else if (algorithm_flags & SC_ALGORITHM_RSA_HASH_SHA384)
		return FINEID_ALGO_HIGH_SHA384;
	else if (algorithm_flags & SC_ALGORITHM_RSA_HASH_SHA512)
		return FINEID_ALGO_HIGH_SHA512;
	else
		return FINEID_ALGO_HIGH_NA;
}


static unsigned int
auth_get_padding(unsigned int algorithm_flags)
{
	if (algorithm_flags & SC_ALGORITHM_RSA_PAD_PKCS1)
		return FINEID_ALGO_LOW_RSASSA_PKCS1;
	else if (algorithm_flags & SC_ALGORITHM_RSA_PAD_ISO9796)
		return FINEID_ALGO_LOW_RSA_9796;
	else if (algorithm_flags & SC_ALGORITHM_RSA_PAD_PSS)
		return FINEID_ALGO_LOW_RSA_PSS;
	else
		return FINEID_ALGO_LOW_NA;
}


static unsigned int
auth_get_ct()
{
	return FINEID_CT_RSAES_OAEP_SHA256;
}


static int
auth_change_security_env(struct sc_card *card)
{
	struct private_driver_data *_driver_data = (struct private_driver_data *) card->drv_data;

	struct sc_apdu apdu;
	int rv;
	unsigned char rsa_sbuf[6] = {
		0x80, 0x01, 0xFF,
		0x84, 0x01, 0xFF
	};

	LOG_FUNC_CALLED(card->ctx);
	sc_log(card->ctx,
	       "operation %i; key_ref 0x%X; algorithm_flags 0x%X",
	       _driver_data->operation, _driver_data->key_ref_msb,
	       _driver_data->algorithm_flags);

	switch (_driver_data->algorithm) {
	case SC_ALGORITHM_RSA:
		if (_driver_data->operation == SC_SEC_OPERATION_SIGN) {
			unsigned int algo = auth_get_algo(_driver_data->algorithm_flags);
			unsigned int padding = auth_get_padding(_driver_data->algorithm_flags);

			if(algo == FINEID_ALGO_HIGH_NA)
				algo = FINEID_ALGO_HIGH_SHA256;

			rsa_sbuf[2] = algo | padding;
			rsa_sbuf[5] = _driver_data->key_ref_msb;

			sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x22, 0x41, 0xB6);
			apdu.lc = sizeof(rsa_sbuf);
			apdu.datalen = sizeof(rsa_sbuf);
			apdu.data = rsa_sbuf;
		}
		else if (_driver_data->operation == SC_SEC_OPERATION_AUTHENTICATE) {
			rsa_sbuf[2] = auth_get_ct();
			rsa_sbuf[5] = _driver_data->key_ref_msb;

			sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x22, 0x41, 0xB8);
			apdu.lc = sizeof(rsa_sbuf);
			apdu.datalen = sizeof(rsa_sbuf);
			apdu.data = rsa_sbuf;
		}
		else if (_driver_data->operation == SC_SEC_OPERATION_DECIPHER) {
			rsa_sbuf[2] = auth_get_ct();
			rsa_sbuf[5] = _driver_data->key_ref_msb;

			sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x22, 0x41, 0xB8);
			apdu.lc = sizeof(rsa_sbuf);
			apdu.datalen = sizeof(rsa_sbuf);
			apdu.data = rsa_sbuf;
		}
		else {
			sc_log(card->ctx, "Invalid crypto operation: %X", _driver_data->operation);
			LOG_FUNC_RETURN(card->ctx, SC_ERROR_NOT_SUPPORTED);
		}

		break;
	default:
		LOG_TEST_RET(card->ctx, SC_ERROR_NOT_SUPPORTED, "Invalid crypto algorithm");
	}

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Card returned error");

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_set_security_env(struct sc_card *card,
		const struct sc_security_env *env, int se_num)
{
	struct private_driver_data *_driver_data = (struct private_driver_data *) card->drv_data;
	int rv;

	LOG_FUNC_CALLED(card->ctx);

	_driver_data->operation = env->operation;
	_driver_data->key_ref_msb = env->key_ref[0];
	_driver_data->algorithm = env->algorithm;
	_driver_data->algorithm_flags = env->algorithm_flags;

	rv = auth_change_security_env(card);

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_restore_security_env(struct sc_card *card, int se_num)
{
	return SC_SUCCESS;
}


static int
auth_compute_signature(struct sc_card *card, const unsigned char *in, size_t ilen,
		unsigned char * out, size_t olen)
{
	struct private_driver_data *_driver_data = (struct private_driver_data *) card->drv_data;
	struct sc_apdu apdu;
	unsigned char instr[SC_MAX_APDU_BUFFER_SIZE];
	unsigned char req[SC_MAX_APDU_BUFFER_SIZE];
	unsigned char resp[SC_MAX_APDU_BUFFER_SIZE];
	size_t ii = 0, reqlen, orglen, blklen = 64;
	int rv;

	LOG_FUNC_CALLED(card->ctx);

	if (!card || !in || !out)   {
		return SC_ERROR_INVALID_ARGUMENTS;
	}

	else if (ilen > 96)   {
		sc_log(card->ctx, "Illegal input length %"SC_FORMAT_LEN_SIZE_T"u", ilen);
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Illegal input length");
	}

	sc_log(card->ctx, "inlen %"SC_FORMAT_LEN_SIZE_T"u, outlen %"SC_FORMAT_LEN_SIZE_T"u", ilen, olen);

	memcpy(&instr, in, ilen);

	if(auth_get_algo(_driver_data->algorithm_flags) == FINEID_ALGO_HIGH_NA &&
	   ilen != 20 && ilen != 28 && ilen != 32 && ilen != 48 && ilen != 64) {
		orglen = ilen;
		sc_log(card->ctx, "Stripping pkcs prefix, cur flags: %X, cur length: %lu",
			_driver_data->algorithm_flags, orglen);

		sc_pkcs1_strip_digest_info_prefix(&_driver_data->algorithm_flags, instr, ilen, instr, &ilen);
		_driver_data->algorithm_flags = _driver_data->algorithm_flags | SC_ALGORITHM_RSA_PAD_PKCS1;
		sc_log(card->ctx, "Stripped pkcs prefix, new flags: %X, new length: %lu",
			_driver_data->algorithm_flags, ilen);

		if(orglen > ilen) {
			rv = auth_change_security_env(card);
			LOG_TEST_RET(card->ctx, rv, "Security env change with new algorithm failed");
		}
	}

	if(ilen>blklen) {
		for (ii=0; ii<ilen-blklen; ii+=blklen)   {
			sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x2A, 0x90, 0x80);
			apdu.datalen = blklen;
			apdu.data = instr+ii;
			apdu.lc = blklen;

			sc_log(card->ctx, "Iterating at offset %lu", ii);
			rv = sc_transmit_apdu(card, &apdu);
			LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
			rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
			LOG_TEST_RET(card->ctx, rv, "Block send with offset failed");
		}
	}

	reqlen = ilen-ii+2;

	memcpy(&req[2], instr+ii, ilen-ii);

	if(auth_get_algo(_driver_data->algorithm_flags) == FINEID_ALGO_HIGH_NA)
		req[0] = FINEID_HASHING_BY_CARD;
	else
		req[0] = FINEID_HASHING_EXTERNALLY;

	req[1] = ilen-ii;

	sc_log(card->ctx, "Finalizing at offset %lu", ii);
	sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x2A, 0x90, 0xA0);
	apdu.datalen = reqlen;
	apdu.data = req;
	apdu.lc = reqlen;

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Last block send failed");

	sc_format_apdu(card, &apdu, SC_APDU_CASE_2_SHORT, 0x2A, 0x9E, 0x9A);
	apdu.le = olen > 256 ? 256 : olen;
	apdu.resp = resp;
	apdu.resplen = olen;

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Signature receiving failed");

	if (apdu.resplen > olen)   {
		sc_log(card->ctx,
		       "Compute signature failed: invalid response length %"SC_FORMAT_LEN_SIZE_T"u",
		       apdu.resplen);
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_CARD_CMD_FAILED);
	}

	memcpy(out, apdu.resp, apdu.resplen);

	LOG_FUNC_RETURN(card->ctx, apdu.resplen);
}


static int
auth_decipher(struct sc_card *card, const unsigned char *in, size_t inlen,
				unsigned char *out, size_t outlen)
{
	struct sc_apdu apdu;
	unsigned char resp[SC_MAX_APDU_BUFFER_SIZE];
	int rv, _inlen = inlen;

	LOG_FUNC_CALLED(card->ctx);
	sc_log(card->ctx,
	       "crgram_len %"SC_FORMAT_LEN_SIZE_T"u;  outlen %"SC_FORMAT_LEN_SIZE_T"u",
	       inlen, outlen);
	if (!out || !outlen || inlen > SC_MAX_APDU_BUFFER_SIZE)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_INVALID_ARGUMENTS);

	sc_format_apdu(card, &apdu, SC_APDU_CASE_4_SHORT, 0x2A, 0x80, 0x86);

	sc_log(card->ctx, "algorithm SC_ALGORITHM_RSA");
	if (inlen % 64)   {
		rv = SC_ERROR_INVALID_ARGUMENTS;
		goto done;
	}

	_inlen = inlen;
	if (_inlen == 256)   {
		apdu.cla |= 0x10;
		apdu.data = in;
		apdu.datalen = 8;
		apdu.resp = resp;
		apdu.resplen = SC_MAX_APDU_BUFFER_SIZE;
		apdu.lc = 8;
		apdu.le = 256;

		rv = sc_transmit_apdu(card, &apdu);
		sc_log(card->ctx, "rv %i", rv);
		LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
		rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
		LOG_TEST_RET(card->ctx, rv, "Card returned error");

		_inlen -= 8;
		in += 8;

		apdu.cla &= ~0x10;
	}

	apdu.data = in;
	apdu.datalen = _inlen;
	apdu.resp = resp;
	apdu.resplen = SC_MAX_APDU_BUFFER_SIZE;
	apdu.lc = _inlen;
	apdu.le = _inlen;

	rv = sc_transmit_apdu(card, &apdu);
	sc_log(card->ctx, "rv %i", rv);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	sc_log(card->ctx, "rv %i", rv);
	LOG_TEST_RET(card->ctx, rv, "Card returned error");

	if (outlen > apdu.resplen)
		outlen = apdu.resplen;

	memcpy(out, apdu.resp, outlen);
	rv = outlen;

done:
	LOG_FUNC_RETURN(card->ctx, rv);
}


/* Return the default AAK for this type of card */
static int
auth_get_default_key(struct sc_card *card, struct sc_cardctl_default_key *data)
{
	LOG_FUNC_RETURN(card->ctx, SC_ERROR_NO_DEFAULT_KEY);
}


static int
auth_card_ctl(struct sc_card *card, unsigned long cmd, void *ptr)
{
	switch (cmd) {
	case SC_CARDCTL_GET_DEFAULT_KEY:
		return auth_get_default_key(card,
				(struct sc_cardctl_default_key *) ptr);
	case SC_CARDCTL_GET_SERIALNR:
		return auth_get_serialnr(card, (struct sc_serial_number *)ptr);
	default:
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_NOT_SUPPORTED);
	}
}


// TODO: Not used atm, see reason at auth_logout()
/*
static int
auth_get_pin_reference (struct sc_card *card, int type, int reference, int cmd, int *out_ref)
{
	if (!out_ref)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_INVALID_ARGUMENTS);

	switch (type) {
	case SC_AC_CHV:
	case SC_AC_CONTEXT_SPECIFIC:
		*out_ref = reference;
		if (reference == 1 || reference == 4)
			if (cmd == SC_PIN_CMD_VERIFY)
				*out_ref |= 0x80;
		break;

	default:
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_INVALID_ARGUMENTS);
	}

	LOG_FUNC_RETURN(card->ctx, SC_SUCCESS);
}
*/


static int
auth_logout(struct sc_card *card)
{
	// TODO: INS 0x2E not present in FINeID
	/*
	struct sc_apdu apdu;
	int ii, rv = 0, pin_ref;
	int reset_flag = 0x20;

	for (ii=0; ii < 4; ii++)   {
		rv = auth_get_pin_reference (card, SC_AC_CHV, ii+1, SC_PIN_CMD_UNBLOCK, &pin_ref);
		LOG_TEST_RET(card->ctx, rv, "Cannot get PIN reference");

		sc_format_apdu(card, &apdu, SC_APDU_CASE_1, 0x2E, 0x00, 0x00);
		apdu.cla = 0x80;
		apdu.p2 = pin_ref | reset_flag;
		rv = sc_transmit_apdu(card, &apdu);
		LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");

	}
	*/

	LOG_FUNC_RETURN(card->ctx, SC_SUCCESS);
}


static int
auth_get_serialnr(struct sc_card *card, struct sc_serial_number *serial)
{
	if (!serial)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_INVALID_ARGUMENTS);

	if (card->serialnr.len==0)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_INTERNAL);

	memcpy(serial, &card->serialnr, sizeof(*serial));

	LOG_FUNC_RETURN(card->ctx, SC_SUCCESS);
}


static int
auth_check_sw(struct sc_card *card, unsigned int sw1, unsigned int sw2)
{
	return iso_ops->check_sw(card, sw1, sw2);
}


static struct sc_card_driver *
sc_get_driver(void)
{
	if (iso_ops == NULL)
		iso_ops = sc_get_iso7816_driver()->ops;

	auth_ops = *iso_ops;
	auth_ops.match_card = auth_match_card;
	auth_ops.init = auth_init;
	auth_ops.finish = auth_finish;
	auth_ops.select_file = auth_select_file;
	auth_ops.list_files = auth_list_files;
	auth_ops.card_ctl = auth_card_ctl;
	auth_ops.set_security_env = auth_set_security_env;
	auth_ops.restore_security_env = auth_restore_security_env;
	auth_ops.compute_signature = auth_compute_signature;
	auth_ops.decipher = auth_decipher;
	auth_ops.process_fci = auth_process_fci;
	auth_ops.logout = auth_logout;
	auth_ops.check_sw = auth_check_sw;
	return &auth_drv;
}


struct sc_card_driver *
sc_get_fineid_driver(void)
{
	return sc_get_driver();
}

#endif /* #ifdef ENABLE_OPENSSL */
