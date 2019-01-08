/*
 * card-fineid.c: Support for FINeID v3 Oberthur smart cards
 *		Oberthur CosmopolIC  FINeID;
 *
 * Copyright (C) 2001, 2002  Juha Yrjölä <juha.yrjola@iki.fi>
 * Copyright (C) 2009  Viktor Tarasov <viktor.tarasov@opentrust.com>,
 *                     OpenTrust <www.opentrust.com>
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

#define OBERTHUR_PIN_LOCAL				0x80
#define OBERTHUR_PIN_REFERENCE_USER		0x81
#define OBERTHUR_PIN_REFERENCE_ONETIME	0x82
#define OBERTHUR_PIN_REFERENCE_SO		0x04
#define OBERTHUR_PIN_REFERENCE_PUK		0x84

static const struct sc_atr_table oberthur_atrs[] = {
	{ "3B:7F:96:00:00:80:31:B8:65:B0:85:03:00:EF:12:00:F6:82:90:00",
		NULL, "FINeID v3", SC_CARD_TYPE_OBERTHUR_FINEID_3, 0, NULL },
	{ NULL, NULL, NULL, 0, 0, NULL }
};

struct auth_senv {
	unsigned int	algorithm;
	int				key_file_id;
	size_t			key_size;
};

struct auth_private_data {
	unsigned char			aid[SC_MAX_AID_SIZE];
	int						aid_len;
	struct sc_pin_cmd_pin	pin_info;
	struct auth_senv		senv;
	long int				sn;
};

struct auth_update_component_info {
	enum SC_CARDCTL_OBERTHUR_KEY_TYPE	type;
	unsigned int						component;
	unsigned char						*data;
	unsigned int						len;
};

static const unsigned char *aidAuthentIC_FINEID =
	(const unsigned char *)"\xA0\x00\x00\x00\x63\x50\x4B\x43\x53\x2D\x31\x35";

static const int lenAidAuthentIC_FINEID = 12;
static const char *nameAidAuthentIC_FINEID = "FINeID v3";

static const struct sc_aid fineid_cm_aid = {
	{0xA0, 0x00, 0x00, 0x00, 0x63, 0x50, 0x4B, 0x43, 0x53, 0x2D, 0x31, 0x35}, 12
};

#define OBERTHUR_AUTH_TYPE_PIN	1
#define OBERTHUR_AUTH_TYPE_PUK	2

#define OBERTHUR_AUTH_MAX_LENGTH_PIN	12
#define OBERTHUR_AUTH_MAX_LENGTH_PUK	12

#define SC_OBERTHUR_MAX_ATTR_SIZE	8

#define PUBKEY_512_ASN1_SIZE	0x4A
#define PUBKEY_1024_ASN1_SIZE	0x8C
#define PUBKEY_2048_ASN1_SIZE	0x10E

static struct sc_file *auth_current_ef = NULL, *auth_current_df = NULL;
static struct sc_card_operations auth_ops;
static struct sc_card_operations *iso_ops;
static struct sc_card_driver auth_drv = {
	"Oberthur IC with FINeID applet",
	"fineid",
	&auth_ops,
	NULL, 0, NULL
};

//static int auth_get_pin_reference (struct sc_card *card,
//	int type, int reference, int cmd, int *out_ref);
static int auth_read_component(struct sc_card *card,
	enum SC_CARDCTL_OBERTHUR_KEY_TYPE type, int num, unsigned char *out, size_t outlen);
static int auth_pin_is_verified(struct sc_card *card, int pin_reference,
	int *tries_left);
static int auth_pin_verify(struct sc_card *card, unsigned int type,
	struct sc_pin_cmd_data *data, int *tries_left);
static int auth_pin_reset(struct sc_card *card, unsigned int type,
	struct sc_pin_cmd_data *data, int *tries_left);
static int auth_create_reference_data (struct sc_card *card,
	struct sc_cardctl_oberthur_createpin_info *args);
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
	struct auth_private_data *data =  (struct auth_private_data *) card->drv_data;
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

	for (ii=0, data->sn = 0; ii < 4; ii++)
		data->sn += (long int)(*(apdu.resp + 15 + ii)) << (3-ii)*8;

	sc_log(card->ctx, "serial number %li/0x%lX", data->sn, data->sn);

	memset(&tmp_path, 0, sizeof(struct sc_path));
	tmp_path.type = SC_PATH_TYPE_DF_NAME;
	
	memcpy(tmp_path.value, aidAuthentIC_FINEID, lenAidAuthentIC_FINEID);
	tmp_path.len = lenAidAuthentIC_FINEID;

	rv = iso_ops->select_file(card, &tmp_path, NULL);
	LOG_TEST_RET(card->ctx, rv, "select parent failed");

	sc_format_path("3F002F00", &tmp_path);
	rv = iso_ops->select_file(card, &tmp_path, &auth_current_df);
	LOG_TEST_RET(card->ctx, rv, "select parent failed");

	sc_format_path("3F002F00", &card->cache.current_path);
	sc_file_dup(&auth_current_ef, auth_current_df);
	
	memcpy(data->aid, aidAuthentIC_FINEID, lenAidAuthentIC_FINEID);
	data->aid_len = lenAidAuthentIC_FINEID;
	card->name = nameAidAuthentIC_FINEID;

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_match_card(struct sc_card *card)
{
	if (_sc_match_atr(card, oberthur_atrs, &card->type) < 0)
		return 0;
	else
		return 1;
}


static int
auth_init(struct sc_card *card)
{
	struct auth_private_data *data;
	struct sc_path path;
	unsigned long flags;
	int rv = 0;

	data = calloc(1, sizeof(struct auth_private_data));
	if (!data)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_OUT_OF_MEMORY);

	card->cla = 0x00;
	card->drv_data = data;

	card->caps |= SC_CARD_CAP_RNG;
	card->caps |= SC_CARD_CAP_USE_FCI_AC;

	if (auth_select_aid(card))   {
		sc_log(card->ctx, "Failed to initialize %s", card->name);
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_CARD, "Failed to initialize");
	}

	flags = SC_ALGORITHM_RSA_PAD_PKCS1 | SC_ALGORITHM_RSA_PAD_ISO9796;
	flags |= SC_ALGORITHM_RSA_HASH_NONE;
	flags |= SC_ALGORITHM_ONBOARD_KEY_GEN;


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
		sc_file_add_acl_entry(file, op, SC_AC_CHV, (acl_byte & 0x0F) | OBERTHUR_PIN_LOCAL);
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
	unsigned char type, attr[SC_OBERTHUR_MAX_ATTR_SIZE];
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
	case 0x11:
		file->type = SC_FILE_TYPE_INTERNAL_EF;
		file->ef_structure = SC_CARDCTL_OBERTHUR_KEY_DES;
		file->size = attr[0]*0x100 + attr[1];
		file->size /= 8;
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
		case SC_CARDCTL_OBERTHUR_KEY_DES:
			add_acl_entry(card, file, SC_AC_OP_UPDATE, attr[0]);
			add_acl_entry(card, file, SC_AC_OP_PSO_DECRYPT, attr[1]);
			add_acl_entry(card, file, SC_AC_OP_PSO_ENCRYPT, attr[2]);
			add_acl_entry(card, file, SC_AC_OP_PSO_COMPUTE_CHECKSUM, attr[3]);
			add_acl_entry(card, file, SC_AC_OP_PSO_VERIFY_CHECKSUM, attr[4]);
			add_acl_entry(card, file, SC_AC_OP_INTERNAL_AUTHENTICATE, attr[5]);
			add_acl_entry(card, file, SC_AC_OP_EXTERNAL_AUTHENTICATE, attr[6]);
			break;
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


static int
auth_set_security_env(struct sc_card *card,
		const struct sc_security_env *env, int se_num)
{
	struct auth_senv *auth_senv = &((struct auth_private_data *) card->drv_data)->senv;
	struct sc_apdu apdu;
	int rv;
	unsigned char rsa_sbuf[6] = {
		0x80, 0x01, 0xFF,
		0x84, 0x01, 0xFF
	};

	LOG_FUNC_CALLED(card->ctx);
	sc_log(card->ctx,
	       "op %i; path %s; key_ref 0x%X; algos 0x%X; flags 0x%lX",
	       env->operation, sc_print_path(&env->file_ref), env->key_ref[0],
	       env->algorithm_flags, env->flags);

	memset(auth_senv, 0, sizeof(struct auth_senv));

	//if (!(env->flags & SC_SEC_ENV_FILE_REF_PRESENT))
	//	LOG_TEST_RET(card->ctx, SC_ERROR_INTERNAL, "Key file is not selected.");

	switch (env->algorithm) {
	case SC_ALGORITHM_RSA:
		if (env->operation == SC_SEC_OPERATION_SIGN) {
			// TODO: Implement and remove hardcoding
			rsa_sbuf[2] = 0x41; // SHA-256 with RSA padding according to ISO 9796-2
			rsa_sbuf[5] = 0x02; // key 2 (signing)

			sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x22, 0x41, 0xB6);
			apdu.lc = sizeof(rsa_sbuf);
			apdu.datalen = sizeof(rsa_sbuf);
			apdu.data = rsa_sbuf;
		}
		else if (env->operation == SC_SEC_OPERATION_DECIPHER) {
			// TODO: Implement and remove hardcoding
			rsa_sbuf[2] = 0x4D; // RSAES OAEP SHA-256
			rsa_sbuf[5] = 0x01; // key 1 (authentication)

			sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x22, 0x41, 0xB8);
			apdu.lc = sizeof(rsa_sbuf);
			apdu.datalen = sizeof(rsa_sbuf);
			apdu.data = rsa_sbuf;
		}
		else {
			sc_log(card->ctx, "Invalid crypto operation: %X", env->operation);
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

	auth_senv->algorithm = env->algorithm;

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
	struct sc_apdu apdu;
	unsigned char req[SC_MAX_APDU_BUFFER_SIZE];
	unsigned char resp[SC_MAX_APDU_BUFFER_SIZE];
	size_t reqlen = ilen + 2;
	int rv;

	LOG_FUNC_CALLED(card->ctx);

	if (!card || !in || !out)   {
		return SC_ERROR_INVALID_ARGUMENTS;
	}
	else if (ilen > 96)   {
		sc_log(card->ctx,
		       "Illegal input length %"SC_FORMAT_LEN_SIZE_T"u",
		       ilen);
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Illegal input length");
	}

	sc_log(card->ctx,
	       "inlen %"SC_FORMAT_LEN_SIZE_T"u, outlen %"SC_FORMAT_LEN_SIZE_T"u",
	       ilen, olen);

	memcpy(&req[2], in, ilen);
	req[0] = 0x80;
	req[1] = ilen;

	sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x2A, 0x90, 0xA0);
	apdu.datalen = reqlen;
	apdu.data = req;
	apdu.lc = reqlen;

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Hash send failed");

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
	case SC_CARDCTL_OBERTHUR_CREATE_PIN:
		return auth_create_reference_data(card,
				(struct sc_cardctl_oberthur_createpin_info *) ptr);
	case SC_CARDCTL_GET_SERIALNR:
		return auth_get_serialnr(card, (struct sc_serial_number *)ptr);
	case SC_CARDCTL_LIFECYCLE_GET:
	case SC_CARDCTL_LIFECYCLE_SET:
		return SC_ERROR_NOT_SUPPORTED;
	default:
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_NOT_SUPPORTED);
	}
}


static int
auth_read_component(struct sc_card *card, enum SC_CARDCTL_OBERTHUR_KEY_TYPE type,
		int num, unsigned char *out, size_t outlen)
{
	struct sc_apdu apdu;
	int rv;
	unsigned char resp[256];

	LOG_FUNC_CALLED(card->ctx);
	sc_log(card->ctx, "num %i, outlen %"SC_FORMAT_LEN_SIZE_T"u, type %i",
	       num, outlen, type);

	if (!outlen || type!=SC_CARDCTL_OBERTHUR_KEY_RSA_PUBLIC)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_INCORRECT_PARAMETERS);

	sc_format_apdu(card, &apdu, SC_APDU_CASE_2_SHORT, 0xB4,	num, 0x00);
	apdu.cla |= 0x80;
	apdu.le = outlen;
	apdu.resp = resp;
	apdu.resplen = sizeof(resp);
	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");

	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Card returned error");

	if (outlen < apdu.resplen)
		LOG_FUNC_RETURN(card->ctx, SC_ERROR_WRONG_LENGTH);

	memcpy(out, apdu.resp, apdu.resplen);
	LOG_FUNC_RETURN(card->ctx, apdu.resplen);
}


static void
auth_init_pin_info(struct sc_card *card, struct sc_pin_cmd_pin *pin,
		unsigned int type)
{
	pin->offset = 0;
	pin->pad_char   = 0x00;
	pin->encoding   = SC_PIN_ENCODING_ASCII;

	if (type == OBERTHUR_AUTH_TYPE_PIN)   {
		pin->max_length = OBERTHUR_AUTH_MAX_LENGTH_PIN;
		pin->pad_length = OBERTHUR_AUTH_MAX_LENGTH_PIN;
	}
	else    {
		pin->max_length = OBERTHUR_AUTH_MAX_LENGTH_PUK;
		pin->pad_length = OBERTHUR_AUTH_MAX_LENGTH_PUK;
	}
}


static int
auth_pin_verify(struct sc_card *card, unsigned int type,
		struct sc_pin_cmd_data *data, int *tries_left)
{
	struct sc_card_driver *iso_drv = sc_get_iso7816_driver();
	int rv;

	LOG_FUNC_CALLED(card->ctx);

	if (type != SC_AC_CHV)
		LOG_TEST_RET(card->ctx, SC_ERROR_NOT_SUPPORTED, "PIN type other then SC_AC_CHV is not supported");

	data->flags |= SC_PIN_CMD_NEED_PADDING;

	auth_init_pin_info(card, &data->pin1, OBERTHUR_AUTH_TYPE_PIN);

	/* User PIN is always local. */
	if (data->pin_reference == OBERTHUR_PIN_REFERENCE_USER
			|| data->pin_reference == OBERTHUR_PIN_REFERENCE_ONETIME)
		data->pin_reference  |= OBERTHUR_PIN_LOCAL;

        rv = auth_pin_is_verified(card, data->pin_reference, tries_left);
    	sc_log(card->ctx, "auth_pin_is_verified returned rv %i", rv);

	/* Return if only PIN status has been asked. */
	if (data->pin1.data && !data->pin1.len)
		LOG_FUNC_RETURN(card->ctx, rv);

	/* Return SUCCESS without verifying if
	 * PIN has been already verified and PIN pad has to be used. */
	if (!rv && !data->pin1.data && !data->pin1.len)
		LOG_FUNC_RETURN(card->ctx, rv);

	rv = iso_drv->ops->pin_cmd(card, data, tries_left);

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_pin_is_verified(struct sc_card *card, int pin_reference, int *tries_left)
{
	struct sc_apdu apdu;
	int rv;

	sc_format_apdu(card, &apdu, SC_APDU_CASE_1, 0x20, 0, pin_reference);

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");

	if (tries_left && apdu.sw1 == 0x63 && (apdu.sw2 & 0xF0) == 0xC0)
		*tries_left = apdu.sw2 & 0x0F;

	/* Replace 'no tries left' with 'auth method blocked' */
	if (apdu.sw1 == 0x63 && apdu.sw2 == 0xC0)    {
		apdu.sw1 = 0x69;
		apdu.sw2 = 0x83;
	}

	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);

	return rv;
}


static int
auth_pin_change(struct sc_card *card, unsigned int type,
		struct sc_pin_cmd_data *data, int *tries_left)
{
	struct sc_card_driver *iso_drv = sc_get_iso7816_driver();
	int rv = SC_ERROR_INTERNAL;

	LOG_FUNC_CALLED(card->ctx);

	if (data->pin1.len && data->pin2.len)   {
		/* Direct unblock style */
		data->flags |= SC_PIN_CMD_NEED_PADDING;
		data->flags &= ~SC_PIN_CMD_USE_PINPAD;
		data->apdu = NULL;

		data->pin_reference &= ~OBERTHUR_PIN_LOCAL;

		auth_init_pin_info(card, &data->pin1, OBERTHUR_AUTH_TYPE_PIN);
		auth_init_pin_info(card, &data->pin2, OBERTHUR_AUTH_TYPE_PIN);

		rv = iso_drv->ops->pin_cmd(card, data, tries_left);
		LOG_TEST_RET(card->ctx, rv, "CMD 'PIN CHANGE' failed");
	}
	else   {
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "'PIN CHANGE' failed");
	}

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_pin_reset_oberthur_style(struct sc_card *card, unsigned int type,
		struct sc_pin_cmd_data *data, int *tries_left)
{
	struct sc_card_driver *iso_drv = sc_get_iso7816_driver();
	struct sc_pin_cmd_data pin_cmd;
	struct sc_path tmp_path;
	struct sc_file *tmp_file = NULL;
	struct sc_apdu apdu;
	unsigned char puk[OBERTHUR_AUTH_MAX_LENGTH_PUK];
	unsigned char ffs1[0x100];
	int rv, rvv, local_pin_reference;

	LOG_FUNC_CALLED(card->ctx);

	local_pin_reference = data->pin_reference & ~OBERTHUR_PIN_LOCAL;

	if (data->pin_reference !=  OBERTHUR_PIN_REFERENCE_USER)
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Oberthur style 'PIN RESET' failed: invalid PIN reference");

	memset(&pin_cmd, 0, sizeof(pin_cmd));
	memset(&tmp_path, 0, sizeof(struct sc_path));

	pin_cmd.pin_type = SC_AC_CHV;
	pin_cmd.cmd = SC_PIN_CMD_VERIFY;
	pin_cmd.pin_reference = OBERTHUR_PIN_REFERENCE_PUK;
	memcpy(&pin_cmd.pin1, &data->pin1, sizeof(pin_cmd.pin1));

	rv = auth_pin_verify(card, SC_AC_CHV, &pin_cmd, tries_left);
	LOG_TEST_RET(card->ctx, rv, "Oberthur style 'PIN RESET' failed: SOPIN verify error");

	sc_format_path("2000", &tmp_path);
	tmp_path.type = SC_PATH_TYPE_FILE_ID;
	rv = iso_ops->select_file(card, &tmp_path, &tmp_file);
	LOG_TEST_RET(card->ctx, rv, "select PUK file");

	if (!tmp_file || tmp_file->size < OBERTHUR_AUTH_MAX_LENGTH_PUK)
		LOG_TEST_RET(card->ctx, SC_ERROR_FILE_TOO_SMALL, "Oberthur style 'PIN RESET' failed");

	rv = iso_ops->read_binary(card, 0, puk, OBERTHUR_AUTH_MAX_LENGTH_PUK, 0);
	LOG_TEST_RET(card->ctx, rv, "read PUK file error");
	if (rv != OBERTHUR_AUTH_MAX_LENGTH_PUK)
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_DATA, "Oberthur style 'PIN RESET' failed");

	memset(ffs1, 0xFF, sizeof(ffs1));
	memcpy(ffs1, puk, rv);

	memset(&pin_cmd, 0, sizeof(pin_cmd));
	pin_cmd.pin_type = SC_AC_CHV;
        pin_cmd.cmd = SC_PIN_CMD_UNBLOCK;
	pin_cmd.pin_reference = local_pin_reference;
	auth_init_pin_info(card, &pin_cmd.pin1, OBERTHUR_AUTH_TYPE_PUK);
	pin_cmd.pin1.data = ffs1;
	pin_cmd.pin1.len = OBERTHUR_AUTH_MAX_LENGTH_PUK;

	if (data->pin2.data)   {
		memcpy(&pin_cmd.pin2, &data->pin2, sizeof(pin_cmd.pin2));
		rv = auth_pin_reset(card, SC_AC_CHV, &pin_cmd, tries_left);
		LOG_FUNC_RETURN(card->ctx, rv);
	}

	sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x2C, 0x00, local_pin_reference);
	apdu.lc = OBERTHUR_AUTH_MAX_LENGTH_PIN  + OBERTHUR_AUTH_MAX_LENGTH_PUK;
	apdu.datalen = OBERTHUR_AUTH_MAX_LENGTH_PIN  + OBERTHUR_AUTH_MAX_LENGTH_PUK;
	apdu.data = ffs1;

	pin_cmd.apdu = &apdu;
	pin_cmd.flags |= SC_PIN_CMD_USE_PINPAD | SC_PIN_CMD_IMPLICIT_CHANGE;

	pin_cmd.pin1.min_length = 4;
	pin_cmd.pin1.max_length = 8;
	pin_cmd.pin1.encoding = SC_PIN_ENCODING_ASCII;
	pin_cmd.pin1.offset = 5;

	pin_cmd.pin2.data = &ffs1[OBERTHUR_AUTH_MAX_LENGTH_PUK];
	pin_cmd.pin2.len = OBERTHUR_AUTH_MAX_LENGTH_PIN;
	pin_cmd.pin2.offset = 5 + OBERTHUR_AUTH_MAX_LENGTH_PUK;
	pin_cmd.pin2.min_length = 4;
	pin_cmd.pin2.max_length = 8;
	pin_cmd.pin2.encoding = SC_PIN_ENCODING_ASCII;

	rvv = iso_drv->ops->pin_cmd(card, &pin_cmd, tries_left);
	if (rvv)
		sc_log(card->ctx,
				"%s: PIN CMD 'VERIFY' with pinpad failed",
				sc_strerror(rvv));

	if (auth_current_ef)
		rv = iso_ops->select_file(card, &auth_current_ef->path, &auth_current_ef);

	if (rv > 0)
		rv = 0;

	LOG_FUNC_RETURN(card->ctx, rv ? rv: rvv);
}


static int
auth_pin_reset(struct sc_card *card, unsigned int type,
		struct sc_pin_cmd_data *data, int *tries_left)
{
	int rv;

	LOG_FUNC_CALLED(card->ctx);

	/* Oberthur unblock style: PUK value is a SOPIN */
	rv = auth_pin_reset_oberthur_style(card, SC_AC_CHV, data, tries_left);
	LOG_TEST_RET(card->ctx, rv, "Oberthur style 'PIN RESET' failed");

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_pin_cmd(struct sc_card *card, struct sc_pin_cmd_data *data, int *tries_left)
{
	int rv = SC_ERROR_INTERNAL;

	LOG_FUNC_CALLED(card->ctx);

	sc_log(card->ctx, "PIN CMD:%i; type:%i; reference:%i; pin1:%p/%i, pin2:%p/%i", data->cmd,
			data->pin_type, data->pin_reference, data->pin1.data, data->pin1.len,
			data->pin2.data, data->pin2.len);

	if (data->pin_type != SC_AC_CHV && data->pin_type != SC_AC_CONTEXT_SPECIFIC)
		LOG_TEST_RET(card->ctx, SC_ERROR_NOT_SUPPORTED, "auth_pin_cmd() unsupported PIN type");

	switch (data->cmd) {
	case SC_PIN_CMD_VERIFY:
		rv = auth_pin_verify(card, SC_AC_CHV, data, tries_left);
		LOG_TEST_RET(card->ctx, rv, "CMD 'PIN VERIFY' failed");
		break;
	case SC_PIN_CMD_CHANGE:
		rv = auth_pin_change(card, SC_AC_CHV, data, tries_left);
		LOG_TEST_RET(card->ctx, rv, "CMD 'PIN VERIFY' failed");
		break;
	case SC_PIN_CMD_UNBLOCK:
		rv = auth_pin_reset(card, SC_AC_CHV, data, tries_left);
		LOG_TEST_RET(card->ctx, rv, "CMD 'PIN VERIFY' failed");
		break;
	case SC_PIN_CMD_GET_INFO:
		auth_init_pin_info(card, &data->pin1, OBERTHUR_AUTH_TYPE_PIN);
		auth_init_pin_info(card, &data->pin2, OBERTHUR_AUTH_TYPE_PIN);
		rv = SC_SUCCESS;
		break;
	default:
		LOG_TEST_RET(card->ctx, SC_ERROR_NOT_SUPPORTED, "Unsupported PIN operation");
	}

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_create_reference_data (struct sc_card *card,
		struct sc_cardctl_oberthur_createpin_info *args)
{
	struct sc_apdu apdu;
	struct sc_pin_cmd_pin pin_info, puk_info;
	int rv, len;
	unsigned char sbuf[SC_MAX_APDU_BUFFER_SIZE];

	LOG_FUNC_CALLED(card->ctx);
	sc_log(card->ctx, "PIN reference %i", args->ref);

	if (args->type != SC_AC_CHV)
		LOG_TEST_RET(card->ctx, SC_ERROR_NOT_SUPPORTED, "Unsupported PIN type");

	if (args->pin_tries < 1 || !args->pin || !args->pin_len)
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Invalid PIN options");

	if (args->ref != OBERTHUR_PIN_REFERENCE_USER && args->ref != OBERTHUR_PIN_REFERENCE_PUK)
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_PIN_REFERENCE, "Invalid PIN reference");

	auth_init_pin_info(card, &puk_info, OBERTHUR_AUTH_TYPE_PUK);
	auth_init_pin_info(card, &pin_info, OBERTHUR_AUTH_TYPE_PIN);

	if (args->puk && args->puk_len && (args->puk_len%puk_info.pad_length))
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Invalid PUK options");

	len = 0;
	sc_log(card->ctx, "len %i", len);
	sbuf[len++] = args->pin_tries;
	sbuf[len++] = pin_info.pad_length;
	sc_log(card->ctx, "len %i", len);
	memset(sbuf + len, pin_info.pad_char, pin_info.pad_length);
	memcpy(sbuf + len, args->pin, args->pin_len);
	len += pin_info.pad_length;
	sc_log(card->ctx, "len %i", len);

	if (args->puk && args->puk_len)   {
		sbuf[len++] = args->puk_tries;
		sbuf[len++] = args->puk_len / puk_info.pad_length;
		sc_log(card->ctx, "len %i", len);
		memcpy(sbuf + len, args->puk, args->puk_len);
		len += args->puk_len;
	}

	sc_log(card->ctx, "len %i", len);
	sc_format_apdu(card, &apdu, SC_APDU_CASE_3_SHORT, 0x24, 1, args->ref & ~OBERTHUR_PIN_LOCAL);
	apdu.data = sbuf;
	apdu.datalen = len;
	apdu.lc = len;

	rv = sc_transmit_apdu(card, &apdu);
	sc_mem_clear(sbuf, sizeof(sbuf));
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");

	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);

	LOG_FUNC_RETURN(card->ctx, rv);
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
auth_read_binary(struct sc_card *card, unsigned int offset,
		unsigned char *buf, size_t count, unsigned long flags)
{
	int rv;
	struct sc_pkcs15_bignum bn[2];
	unsigned char *out = NULL;
	bn[0].data = NULL;
	bn[1].data = NULL;

	LOG_FUNC_CALLED(card->ctx);

	if (!auth_current_ef)
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Invalid auth_current_ef");

	sc_log(card->ctx,
	       "offset %i; size %"SC_FORMAT_LEN_SIZE_T"u; flags 0x%lX",
	       offset, count, flags);
	sc_log(card->ctx,"last selected : magic %X; ef %X",
			auth_current_ef->magic, auth_current_ef->ef_structure);

	if (offset & ~0x7FFF)
		LOG_TEST_RET(card->ctx, SC_ERROR_INVALID_ARGUMENTS, "Invalid file offset");

	if (auth_current_ef->magic==SC_FILE_MAGIC &&
			auth_current_ef->ef_structure == SC_CARDCTL_OBERTHUR_KEY_RSA_PUBLIC)   {
		int jj;
		unsigned char resp[256];
		size_t resp_len, out_len;
		struct sc_pkcs15_pubkey_rsa key;

		resp_len = sizeof(resp);
		rv = auth_read_component(card, SC_CARDCTL_OBERTHUR_KEY_RSA_PUBLIC,
				2, resp, resp_len);
		LOG_TEST_RET(card->ctx, rv, "read component failed");

		for (jj=0; jj<rv && *(resp+jj)==0; jj++)
			;

		bn[0].data = calloc(1, rv - jj);
		if (!bn[0].data) {
			rv = SC_ERROR_OUT_OF_MEMORY;
			goto err;
		}
		bn[0].len = rv - jj;
		memcpy(bn[0].data, resp + jj, rv - jj);

		rv = auth_read_component(card, SC_CARDCTL_OBERTHUR_KEY_RSA_PUBLIC,
				1, resp, resp_len);
		LOG_TEST_GOTO_ERR(card->ctx, rv, "Cannot read RSA public key component");

		bn[1].data = calloc(1, rv);
		if (!bn[1].data) {
			rv = SC_ERROR_OUT_OF_MEMORY;
			goto err;
		}
		bn[1].len = rv;
		memcpy(bn[1].data, resp, rv);

		key.exponent = bn[0];
		key.modulus = bn[1];

		if (sc_pkcs15_encode_pubkey_rsa(card->ctx, &key, &out, &out_len)) {
			rv = SC_ERROR_INVALID_ASN1_OBJECT;
			LOG_TEST_GOTO_ERR(card->ctx, rv, "cannot encode RSA public key");
		}
		else {
			rv  = out_len - offset > count ? count : out_len - offset;
			memcpy(buf, out + offset, rv);

			sc_log_hex(card->ctx, "write_publickey", buf, rv);
		}
	}
	else {
		rv = iso_ops->read_binary(card, offset, buf, count, 0);
	}

err:
	free(bn[0].data);
	free(bn[1].data);
	free(out);

	LOG_FUNC_RETURN(card->ctx, rv);
}


static int
auth_read_record(struct sc_card *card, unsigned int nr_rec,
		unsigned char *buf, size_t count, unsigned long flags)
{
	struct sc_apdu apdu;
	int rv = 0;
	unsigned char recvbuf[SC_MAX_APDU_BUFFER_SIZE];

	sc_log(card->ctx,
	       "auth_read_record(): nr_rec %i; count %"SC_FORMAT_LEN_SIZE_T"u",
	       nr_rec, count);

	sc_format_apdu(card, &apdu, SC_APDU_CASE_2_SHORT, 0xB2, nr_rec, 0);
	apdu.p2 = (flags & SC_RECORD_EF_ID_MASK) << 3;
	if (flags & SC_RECORD_BY_REC_NR)
		apdu.p2 |= 0x04;

	apdu.le = count;
	apdu.resplen = count;
	apdu.resp = recvbuf;

	rv = sc_transmit_apdu(card, &apdu);
	LOG_TEST_RET(card->ctx, rv, "APDU transmit failed");
	if (apdu.resplen == 0)
		LOG_FUNC_RETURN(card->ctx, sc_check_sw(card, apdu.sw1, apdu.sw2));
	memcpy(buf, recvbuf, apdu.resplen);

	rv = sc_check_sw(card, apdu.sw1, apdu.sw2);
	LOG_TEST_RET(card->ctx, rv, "Card returned error");

	LOG_FUNC_RETURN(card->ctx, apdu.resplen);
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
	auth_ops.read_binary = auth_read_binary;
	auth_ops.read_record = auth_read_record;
	auth_ops.card_ctl = auth_card_ctl;
	auth_ops.set_security_env = auth_set_security_env;
	auth_ops.restore_security_env = auth_restore_security_env;
	auth_ops.compute_signature = auth_compute_signature;
	auth_ops.decipher = auth_decipher;
	auth_ops.process_fci = auth_process_fci;
	auth_ops.pin_cmd = auth_pin_cmd;
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
