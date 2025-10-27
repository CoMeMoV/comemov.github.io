/*
 * Type definitions
 */
 
typedef uint8_t     UINT8;
typedef uint8_t     BYTE;
typedef int8_t      INT8;
typedef int         BOOL;
typedef uint16_t    UINT16;
typedef int16_t     INT16;
typedef uint32_t    UINT32;
typedef int32_t     INT32;
typedef uint64_t    UINT64;
typedef int64_t     INT64;

/* Hash algorithm sizes */
#define TPM2_SHA_DIGEST_SIZE     20
#define TPM2_SHA1_DIGEST_SIZE    20
#define TPM2_SHA256_DIGEST_SIZE  32
#define TPM2_SHA384_DIGEST_SIZE  48
#define TPM2_SHA512_DIGEST_SIZE  64
#define TPM2_SM3_256_DIGEST_SIZE 32

/* Encryption algorithm sizes */
#define TPM2_MAX_SYM_BLOCK_SIZE 16
#define TPM2_MAX_SYM_DATA       256
#define TPM2_MAX_ECC_KEY_BYTES  128
#define TPM2_MAX_SYM_KEY_BYTES  32
#define TPM2_MAX_RSA_KEY_BYTES  512

/* Definition of Types for Handles */
typedef UINT32 TPM2_HANDLE;

typedef UINT16 TPM2_ALG_ID;         //71
 /* Definition of TPM2_ALG_ID Constants (From TCG Algorithm Registry) and predicates */

#define TPM2_ALG_ERROR               ((TPM2_ALG_ID) 0x0000)
#define TPM2_ALG_RSA                 ((TPM2_ALG_ID) 0x0001)
#define TPM2_ALG_TDES                ((TPM2_ALG_ID) 0x0003)
#define TPM2_ALG_SHA                 ((TPM2_ALG_ID) 0x0004)
#define TPM2_ALG_SHA1                ((TPM2_ALG_ID) 0x0004)
#define TPM2_ALG_HMAC                ((TPM2_ALG_ID) 0x0005)
#define TPM2_ALG_AES                 ((TPM2_ALG_ID) 0x0006)
#define TPM2_ALG_MGF1                ((TPM2_ALG_ID) 0x0007)
#define TPM2_ALG_KEYEDHASH           ((TPM2_ALG_ID) 0x0008)
#define TPM2_ALG_XOR                 ((TPM2_ALG_ID) 0x000A)
#define TPM2_ALG_SHA256              ((TPM2_ALG_ID) 0x000B)
#define TPM2_ALG_SHA384              ((TPM2_ALG_ID) 0x000C)
#define TPM2_ALG_SHA512              ((TPM2_ALG_ID) 0x000D)
#define TPM2_ALG_NULL                ((TPM2_ALG_ID) 0x0010)
#define TPM2_ALG_SM3_256             ((TPM2_ALG_ID) 0x0012)
#define TPM2_ALG_SM4                 ((TPM2_ALG_ID) 0x0013)
#define TPM2_ALG_RSASSA              ((TPM2_ALG_ID) 0x0014)
#define TPM2_ALG_RSAES               ((TPM2_ALG_ID) 0x0015)
#define TPM2_ALG_RSAPSS              ((TPM2_ALG_ID) 0x0016)
#define TPM2_ALG_OAEP                ((TPM2_ALG_ID) 0x0017)
#define TPM2_ALG_ECDSA               ((TPM2_ALG_ID) 0x0018)
#define TPM2_ALG_ECDH                ((TPM2_ALG_ID) 0x0019)
#define TPM2_ALG_ECDAA               ((TPM2_ALG_ID) 0x001A)
#define TPM2_ALG_SM2                 ((TPM2_ALG_ID) 0x001B)
#define TPM2_ALG_ECSCHNORR           ((TPM2_ALG_ID) 0x001C)
#define TPM2_ALG_ECMQV               ((TPM2_ALG_ID) 0x001D)
#define TPM2_ALG_KDF1_SP800_56A      ((TPM2_ALG_ID) 0x0020)
#define TPM2_ALG_KDF2                ((TPM2_ALG_ID) 0x0021)
#define TPM2_ALG_KDF1_SP800_108      ((TPM2_ALG_ID) 0x0022)
#define TPM2_ALG_ECC                 ((TPM2_ALG_ID) 0x0023)
#define TPM2_ALG_SYMCIPHER           ((TPM2_ALG_ID) 0x0025)
#define TPM2_ALG_CAMELLIA            ((TPM2_ALG_ID) 0x0026)
#define TPM2_ALG_CMAC                ((TPM2_ALG_ID) 0x003F)
#define TPM2_ALG_CTR                 ((TPM2_ALG_ID) 0x0040)
#define TPM2_ALG_SHA3_256            ((TPM2_ALG_ID) 0x0027)
#define TPM2_ALG_SHA3_384            ((TPM2_ALG_ID) 0x0028)
#define TPM2_ALG_SHA3_512            ((TPM2_ALG_ID) 0x0029)
#define TPM2_ALG_OFB                 ((TPM2_ALG_ID) 0x0041)
#define TPM2_ALG_CBC                 ((TPM2_ALG_ID) 0x0042)
#define TPM2_ALG_CFB                 ((TPM2_ALG_ID) 0x0043)
#define TPM2_ALG_ECB                 ((TPM2_ALG_ID) 0x0044)
#define TPM2_ALG_FIRST               ((TPM2_ALG_ID) 0x0001)
#define TPM2_ALG_LAST                ((TPM2_ALG_ID) 0x0044)

/*@
  predicate	correct_tpm2_alg_id(TPM2_ALG_ID alg_id) =
    alg_id \in 
      {
        TPM2_ALG_ERROR, TPM2_ALG_RSA, TPM2_ALG_TDES, TPM2_ALG_SHA, TPM2_ALG_SHA1, 
        TPM2_ALG_HMAC, TPM2_ALG_AES, TPM2_ALG_MGF1, TPM2_ALG_KEYEDHASH, TPM2_ALG_XOR, 
        TPM2_ALG_SHA256, TPM2_ALG_SHA384 ,TPM2_ALG_SHA512, TPM2_ALG_NULL, TPM2_ALG_SM3_256,
        TPM2_ALG_SM4, TPM2_ALG_RSASSA, TPM2_ALG_RSAES, TPM2_ALG_RSAPSS, TPM2_ALG_OAEP,
        TPM2_ALG_ECDSA, TPM2_ALG_ECDH , TPM2_ALG_ECDAA, TPM2_ALG_SM2, TPM2_ALG_ECSCHNORR,
        TPM2_ALG_ECMQV, TPM2_ALG_KDF1_SP800_56A, TPM2_ALG_KDF2, TPM2_ALG_KDF1_SP800_108, TPM2_ALG_ECC,
        TPM2_ALG_SYMCIPHER, TPM2_ALG_CAMELLIA, TPM2_ALG_CMAC, TPM2_ALG_CTR, TPM2_ALG_SHA3_256,
        TPM2_ALG_SHA3_384, TPM2_ALG_SHA3_512, TPM2_ALG_OFB, TPM2_ALG_CBC, TPM2_ALG_CFB,
        TPM2_ALG_ECB, TPM2_ALG_FIRST, TPM2_ALG_LAST
      }
    ;
*/

/*@
  predicate	valid_tpm2_alg_id(TPM2_ALG_ID * alg_id) =
    \valid(alg_id)
    && correct_tpm2_alg_id(*alg_id)
  ;
*/


/* From TCG Algorithm Registry: Definition of TPM2_ECC_CURVE Constants */           //143
typedef UINT16                TPM2_ECC_CURVE;
#define TPM2_ECC_NONE         ((TPM2_ECC_CURVE) 0x0000)
#define TPM2_ECC_NIST_P192    ((TPM2_ECC_CURVE) 0x0001)
#define TPM2_ECC_NIST_P224    ((TPM2_ECC_CURVE) 0x0002)
#define TPM2_ECC_NIST_P256    ((TPM2_ECC_CURVE) 0x0003)
#define TPM2_ECC_NIST_P384    ((TPM2_ECC_CURVE) 0x0004)
#define TPM2_ECC_NIST_P521    ((TPM2_ECC_CURVE) 0x0005)
#define TPM2_ECC_BN_P256      ((TPM2_ECC_CURVE) 0x0010)
#define TPM2_ECC_BN_P638      ((TPM2_ECC_CURVE) 0x0011)
#define TPM2_ECC_SM2_P256     ((TPM2_ECC_CURVE) 0x0020)


/* Definition of UINT8 TPM2_SE Constants <IN> */
typedef UINT8 TPM2_SE;
#define TPM2_SE_HMAC    ((TPM2_SE) 0x00)
#define TPM2_SE_POLICY  ((TPM2_SE) 0x01)
#define TPM2_SE_TRIAL   ((TPM2_SE) 0x03) /* The policy session is being used to compute the policyHash and not for command authorization.This setting modifies some policy commands and prevents session from being used to authorize a command. */

/*@
  predicate	correct_tpm2_se(TPM2_SE tpm2_se) =
    tpm2_se \in {TPM2_SE_HMAC, TPM2_SE_POLICY, TPM2_SE_TRIAL};
*/

/*@
  predicate	valid_tpm2_se(TPM2_SE * tpm2_se) =
    \valid(tpm2_se)
	&& correct_tpm2_se(*tpm2_se)
	;
*/


typedef UINT8 TPMA_SESSION;
/* Definition of UINT8 TPMA_SESSION Bits <INOUT>, constants and predicates */
#define TPMA_SESSION_CONTINUESESSION ((TPMA_SESSION) 0x00000001) /* SET 1 In a command this setting indicates that the session is to remain active after successful completion of the command. In a response it indicates that the session is still active. If SET in the command this attribute shall be SET in the response. CLEAR 0 In a command this setting indicates that the TPM should close the session and flush any related context when the command completes successfully. In a response it indicates that the session is closed and the context is no longer active. This attribute has no meaning for a password authorization and the TPM will allow any setting of the attribute in the command and SET the attribute in the response. This attribute will only be CLEAR in one response for a logical session. If the attribute is CLEAR the context associated with the session is no longer in use and the space is available. A session created after another session is ended may have the same handle but logically is not the same session. This attribute has no effect if the command does not complete successfully. */
#define TPMA_SESSION_AUDITEXCLUSIVE  ((TPMA_SESSION) 0x00000002) /* SET 1 In a command this setting indicates that the command should only be executed if the session is exclusive at the start of the command. In a response it indicates that the session is exclusive. This setting is only allowed if the audit attribute is SET TPM2_RC_ATTRIBUTES. CLEAR 0 In a command indicates that the session need not be exclusive at the start of the command.  In a response indicates that the session is not exclusive. In this revision if audit is CLEAR auditExclusive must be CLEAR in the command and will be CLEAR in the response.  In a future revision this bit may have a different meaning if audit is CLEAR. See Exclusive Audit Session clause in TPM 2.0 Part 1. */
#define TPMA_SESSION_AUDITRESET      ((TPMA_SESSION) 0x00000004) /* SET 1 In a command this setting indicates that the audit digest of the session should be initialized and the exclusive status of the session SET. This setting is only allowed if the audit attribute is SET TPM2_RC_ATTRIBUTES. CLEAR 0 In a command indicates that the audit digest should not be initialized. This bit is always CLEAR in a response. In this revision if audit is CLEAR auditReset must be clear in the command and will be CLEAR in the response.  In a future revision this bit may have a different meaning if audit is CLEAR. */
#define TPMA_SESSION_RESERVED1_MASK  ((TPMA_SESSION) 0x00000018) /* shall be CLEAR */
#define TPMA_SESSION_DECRYPT         ((TPMA_SESSION) 0x00000020) /* SET 1 In a command this setting indicates that the first parameter in the command is symmetrically encrypted using the parameter encryption scheme described in TPM 2.0 Part 1. The TPM will decrypt the parameter after performing any HMAC computations and before unmarshaling the parameter. In a response the attribute is copied from the request but has no effect on the response. CLEAR 0 Session not used for encryption. For a password authorization this attribute will be CLEAR in both the command and response. This attribute may only be SET in one session per command. This attribute may be SET in a session that is not associated with a command handle. Such a session is provided for purposes of encrypting a parameter and not for authorization. This attribute may be SET in combination with any other session attributes. This attribute may only be SET if the first parameter of the command is a sized buffer TPM2B_. */
#define TPMA_SESSION_ENCRYPT         ((TPMA_SESSION) 0x00000040) /* SET 1 In a command this setting indicates that the TPM should use this session to encrypt the first parameter in the response. In a response it indicates that the attribute was set in the command and that the TPM used the session to encrypt the first parameter in the response using the parameter encryption scheme described in TPM 2.0 Part 1. CLEAR 0 Session not used for encryption. For a password authorization this attribute will be CLEAR in both the command and response. This attribute may only be SET in one session per command. This attribute may be SET in a session that is not associated with a command handle. Such a session is provided for purposes of encrypting a parameter and not for authorization. This attribute may only be SET if the first parameter of a response is a sized buffer TPM2B_. */
#define TPMA_SESSION_AUDIT           ((TPMA_SESSION) 0x00000080) /* SET 1 In a command or response this setting indicates that the session is for audit and that auditExclusive and auditReset have meaning. This session may also be used for authorization encryption or decryption. The encrypted and encrypt fields may be SET or CLEAR. CLEAR 0 Session is not used for audit. This attribute may only be SET in one session per command or response. If SET in the command then this attribute will be SET in the response. */

/*@
  predicate	correct_tpma_session(TPMA_SESSION tpma_session) =
    tpma_session \in 
      {
        TPMA_SESSION_CONTINUESESSION, TPMA_SESSION_AUDITEXCLUSIVE, 
		TPMA_SESSION_AUDITRESET, TPMA_SESSION_RESERVED1_MASK, 
		TPMA_SESSION_DECRYPT, TPMA_SESSION_ENCRYPT, 
		TPMA_SESSION_AUDIT
      }
    ;
*/

/*@
  predicate	valid_tpma_session(TPMA_SESSION * tpma_session) =
    \valid(tpma_session)
    && correct_tpma_session(*tpma_session)
  ;
*/




typedef UINT16 TPM2_KEY_BITS;           /* a key size in bits */        //283

/* Definition of UINT32 TPMA_OBJECT Bits */         //718
typedef uint32_t TPMA_OBJECT;

/* Definition of TPM2_ALG_ID TPMI_ALG_HASH Type */         //944
typedef TPM2_ALG_ID TPMI_ALG_HASH;

/* Definition of TPM2_ALG_ID TPMI_ALG_SYM Type */
typedef TPM2_ALG_ID TPMI_ALG_SYM;

/* Definition of TPM2_ALG_ID TPMI_ALG_SYM_OBJECT Type */        //953
typedef TPM2_ALG_ID TPMI_ALG_SYM_OBJECT;

/* Definition of TPM2_ALG_ID TPMI_ALG_SYM_MODE Type */      //956
typedef TPM2_ALG_ID TPMI_ALG_SYM_MODE;

/* Definition of TPM2_ALG_ID TPMI_ALG_KDF Type */           //959
typedef TPM2_ALG_ID TPMI_ALG_KDF;


/* Definition of  AES TPM2_KEY_BITS TPMI_AES_KEY_BITS   Type */         //1463
typedef TPM2_KEY_BITS TPMI_AES_KEY_BITS;

/* Definition of  SM4 TPM2_KEY_BITS TPMI_SM4_KEY_BITS   Type */         //1465
typedef TPM2_KEY_BITS TPMI_SM4_KEY_BITS;

/* Definition of  CAMELLIA TPM2_KEY_BITS TPMI_CAMELLIA_KEY_BITS   Type */       //1467
typedef TPM2_KEY_BITS TPMI_CAMELLIA_KEY_BITS;



/*
 * Return Codes
 */
/* The return type for all TSS2 functions */
typedef uint32_t TSS2_RC;


/******************************************************************************/
/********************************* ESYS_TR ************************************/
/******************************************************************************/

typedef uint32_t ESYS_TR;
// ESYS_TR values and predicates
#define ESYS_TR_NONE     0xfffU
#define ESYS_TR_PASSWORD 0x0ffU
#define ESYS_TR_PCR0      0U
#define ESYS_TR_PCR1      1U
#define ESYS_TR_PCR2      2U
#define ESYS_TR_PCR3      3U
#define ESYS_TR_PCR4      4U
#define ESYS_TR_PCR5      5U
#define ESYS_TR_PCR6      6U
#define ESYS_TR_PCR7      7U
#define ESYS_TR_PCR8      8U
#define ESYS_TR_PCR9      9U
#define ESYS_TR_PCR10    10U
#define ESYS_TR_PCR11    11U
#define ESYS_TR_PCR12    12U
#define ESYS_TR_PCR13    13U
#define ESYS_TR_PCR14    14U
#define ESYS_TR_PCR15    15U
#define ESYS_TR_PCR16    16U
#define ESYS_TR_PCR17    17U
#define ESYS_TR_PCR18    18U
#define ESYS_TR_PCR19    19U
#define ESYS_TR_PCR20    20U
#define ESYS_TR_PCR21    21U
#define ESYS_TR_PCR22    22U
#define ESYS_TR_PCR23    23U
#define ESYS_TR_PCR24    24U
#define ESYS_TR_PCR25    25U
#define ESYS_TR_PCR26    26U
#define ESYS_TR_PCR27    27U
#define ESYS_TR_PCR28    28U
#define ESYS_TR_PCR29    29U
#define ESYS_TR_PCR30    30U
#define ESYS_TR_PCR31    31U

/* From TPM_RH_CONSTANTS */
#define ESYS_TR_RH_OWNER       0x101U
#define ESYS_TR_RH_NULL        0x107U
#define ESYS_TR_RH_LOCKOUT     0x10AU
#define ESYS_TR_RH_ENDORSEMENT 0x10BU
#define ESYS_TR_RH_PLATFORM    0x10CU
#define ESYS_TR_RH_PLATFORM_NV 0x10DU

#define ESYS_TR_RH_AUTH_FIRST  0x110U
#define ESYS_TR_RH_AUTH(x) (ESYS_TR_RH_AUTH_FIRST + (ESYS_TR)(x))
#define ESYS_TR_RH_ACT_FIRST  0x120U
#define ESYS_TR_RH_ACT(x) (ESYS_TR_RH_ACT_FIRST + (ESYS_TR)(x))
#define ESYS_TR_RH_ACT_LAST  0x12FU

/*@ logic \list<integer> prealloc_esys_tr_list = [|
		ESYS_TR_NONE, ESYS_TR_PASSWORD, ESYS_TR_PCR0, ESYS_TR_PCR1, ESYS_TR_PCR2, 
		ESYS_TR_PCR3, ESYS_TR_PCR4, ESYS_TR_PCR5, ESYS_TR_PCR6, ESYS_TR_PCR7, 
		ESYS_TR_PCR8, ESYS_TR_PCR9, ESYS_TR_PCR10, ESYS_TR_PCR10, ESYS_TR_PCR11,
		ESYS_TR_PCR12, ESYS_TR_PCR13, ESYS_TR_PCR14, ESYS_TR_PCR15, ESYS_TR_PCR16,
		ESYS_TR_PCR17, ESYS_TR_PCR18, ESYS_TR_PCR19, ESYS_TR_PCR20, ESYS_TR_PCR21,
		ESYS_TR_PCR22, ESYS_TR_PCR23, ESYS_TR_PCR24, ESYS_TR_PCR25, ESYS_TR_PCR26,
		ESYS_TR_PCR27, ESYS_TR_PCR28, ESYS_TR_PCR29, ESYS_TR_PCR30, ESYS_TR_PCR31,
		ESYS_TR_RH_OWNER, ESYS_TR_RH_NULL, ESYS_TR_RH_LOCKOUT, ESYS_TR_RH_PLATFORM, ESYS_TR_RH_PLATFORM_NV,
		ESYS_TR_RH_AUTH_FIRST, ESYS_TR_RH_ACT_FIRST
  |];
*/

/*@
  predicate	is_prealloc_esys_tr(ESYS_TR esys_tr) =
  \exists integer index;
    0 <= index < \length(prealloc_esys_tr_list)
      ==> (esys_tr == \nth(prealloc_esys_tr_list, index)
        || esys_tr == ESYS_TR_RH_AUTH_FIRST + \nth(prealloc_esys_tr_list, index)
        || esys_tr == ESYS_TR_RH_ACT_FIRST + \nth(prealloc_esys_tr_list, index)
        || esys_tr == ESYS_TR_RH_ACT_LAST
      );
*/

/*@
  predicate	is_correct_esys_tr_esys_object(ESYS_TR esys_tr) =
    !(esys_tr < 0x1000) && !is_prealloc_esys_tr(esys_tr)
  ;
*/

/*@
  predicate	correct_esys_tr(ESYS_TR esys_tr) =
    is_prealloc_esys_tr(esys_tr) || is_correct_esys_tr_esys_object(esys_tr)
  ;
*/

/*@
  predicate	valid_esys_tr(ESYS_TR * esys_tr) =
  \valid(esys_tr)
  && correct_esys_tr(*esys_tr)
  ;
*/




/** Selector type for esys resources
 */
typedef UINT32                  IESYSC_RESOURCE_TYPE;
 // IESYSC_RESOURCE_TYPE values and predicates
/** Type of resource
 */
typedef UINT32 IESYSC_RESOURCE_TYPE_CONSTANT;
#define IESYSC_KEY_RSRC                1    /**< Tag for key resource */
#define IESYSC_NV_RSRC                 2    /**< Tag for NV Ram resource */
#define IESYSC_SESSION_RSRC            3    /**< Tag for session resources */
#define IESYSC_DEGRADED_SESSION_RSRC   4    /**< Tag for degraded session resources */
#define IESYSC_WITHOUT_MISC_RSRC       0    /**< Tag for other resources, e.g. PCR register, hierarchies */

/*@ logic \list<integer> rsrcType_list = [| IESYSC_KEY_RSRC, IESYSC_NV_RSRC, IESYSC_SESSION_RSRC,
                                                IESYSC_DEGRADED_SESSION_RSRC, IESYSC_WITHOUT_MISC_RSRC |];
*/

/*@
  predicate	correct_iesysc_rsrc(IESYSC_RESOURCE_TYPE rsrcType) =
  \exists integer index;
    0 <= index < \length(rsrcType_list)
      ==> (rsrcType == \nth(rsrcType_list, index));
*/


/** Type to indicate parameter encryption (by TPM)
 */
typedef UINT32 IESYSC_PARAM_ENCRYPT;
#define ENCRYPT                        1    /**< Parameter encryption by TPM */
#define NO_ENCRYPT                     0    /**< No parameter encryption by TPM */

/** Type to indicate parameter decryption (by TPM)
 */
typedef UINT32 IESYSC_PARAM_DECRYPT;
#define DECRYPT                        1    /**< Parameter decryption by TPM */
#define NO_DECRYPT                     0    /**< No parameter decryption by TPM */

/** Type of policy authorization
 */
typedef UINT32 IESYSC_TYPE_POLICY_AUTH;
#define POLICY_PASSWORD                2    /**< Marker to include auth value of the authorized object */
#define POLICY_AUTH                    1    /**< Marker to include the auth value in the HMAC key */
#define NO_POLICY_AUTH                 0    /**< no special handling */

/******************************************************************************/
/**************************** Digest-like structs *****************************/
/******************************************************************************/

/* Definition of TPMU_HA Union <INOUT S> */
typedef union TPMU_HA TPMU_HA;           //TODO struct <--> union
union TPMU_HA {                          //TODO struct <--> union
// typedef struct TPMU_HA TPMU_HA;             //TODO struct <--> union
// struct TPMU_HA {                            //TODO struct <--> union
    BYTE sha1[TPM2_SHA1_DIGEST_SIZE];
    BYTE sha256[TPM2_SHA256_DIGEST_SIZE];
    BYTE sha384[TPM2_SHA384_DIGEST_SIZE];
    BYTE sha512[TPM2_SHA512_DIGEST_SIZE];
    BYTE sm3_256[TPM2_SM3_256_DIGEST_SIZE];
};


/* Definition of TPM2_HANDLE TPMI_RH_NV_INDEX Type <INOUT> */       //935
typedef TPM2_HANDLE TPMI_RH_NV_INDEX;

/* Definition of TPMS_EMPTY Structure <INOUT> */        //977
typedef struct TPMS_EMPTY TPMS_EMPTY;
struct TPMS_EMPTY {
    BYTE empty[1]; /* a structure with no member */
};

 // TPM2B_DIGEST, TPM2B_DATA and digest casts          //1007


/* Definition of TPM2B_DIGEST Structure */
typedef struct TPM2B_DIGEST TPM2B_DIGEST;
struct TPM2B_DIGEST {
    UINT16 size;
    BYTE buffer[sizeof(TPMU_HA)];
};

/*@
  predicate zero_tpm2b_digest(TPM2B_DIGEST digest) =
    digest.size == 0
    // && digest.buffer[0 .. sizeof(TPMU_HA) - 1] == { (BYTE) 0 }
    && \forall int i; 0 <= i  < sizeof(TPMU_HA) ==>
        digest.buffer[i] == (BYTE) 0
    ;
*/

/*@
  predicate valid_tpm2b_digest(TPM2B_DIGEST *digest) =
    \valid(digest)
    && 0 <= digest->size <= sizeof(TPMU_HA)
    && 0 < digest->size ==> \valid(digest->buffer + (0 .. (digest->size - 1)));
*/

/*@
  predicate valid_read_tpm2b_digest(TPM2B_DIGEST *digest) =
    \valid_read(digest)
	&& 0 <= digest->size <= sizeof(TPMU_HA)
    && 0 < digest->size ==> \valid_read(digest->buffer + (0 .. (digest->size - 1)));
*/



/* Definition of TPM2B_DATA Structure */
typedef struct TPM2B_DATA TPM2B_DATA;
struct TPM2B_DATA {
    UINT16 size;
    BYTE buffer[sizeof(TPMU_HA)];
};

/*@
  predicate zero_tpm2b_data(TPM2B_DATA data) =
    data.size == 0
    // && data.buffer[0 .. sizeof(TPMU_HA) - 1] == { (BYTE) 0 }
    && \forall int i; 0 <= i  < sizeof(TPMU_HA) ==>
        data.buffer[i] == (BYTE) 0
    ;
*/

/*@
  predicate valid_tpm2b_data(TPM2B_DATA *data) =
    \valid(data)
    && 0 < data->size <= sizeof(TPMU_HA)
    && \valid(data->buffer + (0 .. (data->size - 1)));
*/

/*@
  predicate valid_read_tpm2b_data(TPM2B_DATA *data) =
    \valid_read(data)
	&& 0 < data->size <= sizeof(TPMU_HA)
    && \valid_read(data->buffer + (0 .. (data->size - 1)));
*/


/* Definition of Types for TPM2B_NONCE */
typedef TPM2B_DIGEST  TPM2B_NONCE; /* size limited to the same as the digest structure */

/*@
  predicate valid_tpm2b_nonce(TPM2B_NONCE *nonce) =
    valid_tpm2b_digest((TPM2B_DIGEST *) nonce)
	;
*/

/*@
  predicate valid_read_tpm2b_nonce(TPM2B_NONCE *nonce) =
    valid_read_tpm2b_digest((TPM2B_DIGEST *) nonce)
	;
*/


/* Definition of Types for TPM2B_AUTH */
typedef TPM2B_DIGEST  TPM2B_AUTH; /* size limited to the same as the digest structure */

/*@
  predicate valid_tpm2b_auth(TPM2B_AUTH *auth) =
    valid_tpm2b_digest((TPM2B_DIGEST *) auth)
	;
*/

/*@
  predicate valid_read_tpm2b_auth(TPM2B_AUTH *auth) =
    valid_read_tpm2b_digest((TPM2B_DIGEST *) auth)
	;
*/



// TPM2B_NAME

/* Definition of TPMT_HA Structure <INOUT> */
typedef struct TPMT_HA TPMT_HA;
struct TPMT_HA {
    TPMI_ALG_HASH hashAlg; /* selector of the hash contained in the digest that implies the size of the digest. NOTE The leading + on the type indicates that this structure should pass an indication to the unmarshaling function for TPMI_ALG_HASH so that TPM2_ALG_NULL will be allowed if a use of a TPMT_HA allows TPM2_ALG_NULL. */
    TPMU_HA digest;        /* the digest data */
};

/* Definition of TPMU_NAME Union <> */
typedef union TPMU_NAME TPMU_NAME;       //TODO struct <--> union
union TPMU_NAME {                        //TODO struct <--> union
// typedef struct TPMU_NAME TPMU_NAME;         //TODO struct <--> union
// struct TPMU_NAME {                          //TODO struct <--> union
    TPMT_HA digest;     /* when the Name is a digest */
    TPM2_HANDLE handle; /* when the Name is a handle */
};


/* Definition of TPM2B_NAME Structure */
typedef struct TPM2B_NAME TPM2B_NAME;
struct TPM2B_NAME {
    UINT16 size;
    BYTE name[sizeof(TPMU_NAME)];
};

/*@
  predicate zero_tpm2b_name(TPM2B_NAME tpm2b_name) =
    tpm2b_name.size == 0
    // && tpm2b_name.name[0 .. sizeof(TPMU_NAME) - 1] == { (BYTE) 0 }
    && \forall int i; 0 <= i  < sizeof(TPMU_NAME) ==>
        tpm2b_name.name[i] == (BYTE) 0
    ;
*/

/*@
  predicate valid_tpm2b_name(TPM2B_NAME *name) =
    \valid(name)
    && 0 <= name->size < sizeof(TPMU_NAME)
    && \valid(name->name + (0 .. (name->size - 1)));
*/

/* Definition of TPMU_SYM_KEY_BITS Union */         //1472
typedef union TPMU_SYM_KEY_BITS TPMU_SYM_KEY_BITS;       //TODO struct <--> union
union TPMU_SYM_KEY_BITS {                                //TODO struct <--> union
// typedef struct TPMU_SYM_KEY_BITS TPMU_SYM_KEY_BITS;         //TODO struct <--> union
// struct TPMU_SYM_KEY_BITS {                                  //TODO struct <--> union
    TPMI_AES_KEY_BITS aes;                /* all symmetric algorithms */
    TPMI_SM4_KEY_BITS sm4;                /* all symmetric algorithms */
    TPMI_CAMELLIA_KEY_BITS camellia;      /* all symmetric algorithms */
    TPM2_KEY_BITS sym;                    /* when selector may be any of the symmetric block ciphers */
    TPMI_ALG_HASH exclusiveOr;            /* overload for using xor. NOTE TPM2_ALG_NULL is not allowed */
};

/*@
  predicate zero_tpmu_sym_key_bits(TPMU_SYM_KEY_BITS tpmu_bits) =
    tpmu_bits.aes == 0
    || tpmu_bits.sm4 == 0
    || tpmu_bits.camellia == 0
    || tpmu_bits.sym == 0
    || tpmu_bits.exclusiveOr == 0;
*/

/*@
  predicate correct_tpmu_sym_key_bits(TPMU_SYM_KEY_BITS tpmu_bits) =
    0 <= tpmu_bits.aes < 65536
    || 0 <= tpmu_bits.sm4 < 65536
    || 0 <= tpmu_bits.camellia < 65536
    || 0 <= tpmu_bits.sym < 65536
    || correct_tpm2_alg_id(tpmu_bits.exclusiveOr);
*/


/* Definition of TPMU_SYM_MODE Union */
typedef union TPMU_SYM_MODE TPMU_SYM_MODE;    //1490     //TODO struct <--> union
union TPMU_SYM_MODE {                                    //TODO struct <--> union
// typedef struct TPMU_SYM_MODE TPMU_SYM_MODE;    //1490       //TODO struct <--> union
// struct TPMU_SYM_MODE {                                      //TODO struct <--> union
    TPMI_ALG_SYM_MODE aes;
            // uint16_t, ./include/tss2/tss2_tpm2_types.h
    TPMI_ALG_SYM_MODE sm4;
            // uint16_t, ./include/tss2/tss2_tpm2_types.h
    TPMI_ALG_SYM_MODE camellia;
            // uint16_t, ./include/tss2/tss2_tpm2_types.h
    TPMI_ALG_SYM_MODE sym;  /* when selector may be any of the symmetric block ciphers */
            // uint16_t, ./include/tss2/tss2_tpm2_types.h
};

/*@
  predicate zero_tpmu_sym_mode(TPMU_SYM_MODE tpmu_sym_mode) =
    tpmu_sym_mode.aes == 0
    || tpmu_sym_mode.sm4 == 0
    || tpmu_sym_mode.camellia == 0
    || tpmu_sym_mode.sym == 0;
*/



/*@
  predicate correct_tpmu_sym_mode(TPMU_SYM_MODE tpmu_sym_mode) =
    correct_tpm2_alg_id(tpmu_sym_mode.aes)
    || correct_tpm2_alg_id(tpmu_sym_mode.sm4)
    || correct_tpm2_alg_id(tpmu_sym_mode.camellia)
    || correct_tpm2_alg_id(tpmu_sym_mode.sym);
*/

/* Definition of TPMT_SYM_DEF_OBJECT Structure */           //1531
typedef struct TPMT_SYM_DEF_OBJECT TPMT_SYM_DEF_OBJECT;
struct TPMT_SYM_DEF_OBJECT {
    TPMI_ALG_SYM_OBJECT algorithm; /* selects a symmetric block cipher */
    TPMU_SYM_KEY_BITS keyBits;     /* the key size */
    TPMU_SYM_MODE mode;            /* default mode */
};

/*@
  predicate zero_tpmt_sym_def_object(TPMT_SYM_DEF_OBJECT tpmt_obj) =
    tpmt_obj.algorithm == 0
	&& zero_tpmu_sym_key_bits(tpmt_obj.keyBits)
	&& zero_tpmu_sym_mode(tpmt_obj.mode);
*/

/*@
  predicate correct_tpmt_sym_def_object(TPMT_SYM_DEF_OBJECT tpmt_obj) =
    correct_tpm2_alg_id(tpmt_obj.algorithm)
	&& correct_tpmu_sym_key_bits(tpmt_obj.keyBits)
	&& correct_tpmu_sym_mode(tpmt_obj.mode);
*/

/* Definition of TPMS_SYMCIPHER_PARMS Structure */          //1553
typedef struct TPMS_SYMCIPHER_PARMS TPMS_SYMCIPHER_PARMS;
struct TPMS_SYMCIPHER_PARMS {
    TPMT_SYM_DEF_OBJECT sym;   /* a symmetric block cipher */
};


/*@
  predicate zero_tpms_symcipher_parms(TPMS_SYMCIPHER_PARMS tpms_symcipher_parms) =
    zero_tpmt_sym_def_object(tpms_symcipher_parms.sym);
*/

/*@
  predicate correct_tpms_symcipher_parms(TPMS_SYMCIPHER_PARMS *tpms_symcipher_parms) =
    \valid(tpms_symcipher_parms)
    && correct_tpmt_sym_def_object(tpms_symcipher_parms->sym);
*/

/* Definition of TPMS_SCHEME_HASH Structure */      //1621
typedef struct TPMS_SCHEME_HASH TPMS_SCHEME_HASH;
struct TPMS_SCHEME_HASH {
    TPMI_ALG_HASH hashAlg; /* the hash algorithm used to digest the message */
};

/*@
  predicate correct_tpms_scheme_hash(TPMS_SCHEME_HASH scheme) =
    correct_tpm2_alg_id(scheme.hashAlg);
*/


/* Definition of ECC TPMS_SCHEME_ECDAA Structure */     //1631
typedef struct TPMS_SCHEME_ECDAA TPMS_SCHEME_ECDAA;
struct TPMS_SCHEME_ECDAA {
    TPMI_ALG_HASH hashAlg; /* the hash algorithm used to digest the message */
    UINT16 count;          /* the counter value that is used between TPM2_Commit and the sign operation */
};

/*@
  predicate correct_tpms_scheme_ecdaa(TPMS_SCHEME_ECDAA tpms_scheme) =
    correct_tpm2_alg_id(tpms_scheme.hashAlg) 
	&& 0 <= tpms_scheme.count < 65536;
*/

/* Definition of TPM2_ALG_ID TPMI_ALG_KEYEDHASH_SCHEME Type */      //1644
typedef TPM2_ALG_ID TPMI_ALG_KEYEDHASH_SCHEME;

/* Definition of Types for HMAC_SIG_SCHEME */           //1647
typedef TPMS_SCHEME_HASH TPMS_SCHEME_HMAC;

/* Definition of TPMS_SCHEME_XOR Structure */       //1650
typedef struct TPMS_SCHEME_XOR TPMS_SCHEME_XOR;
struct TPMS_SCHEME_XOR {
    TPMI_ALG_HASH hashAlg; /* the hash algorithm used to digest the message */
    TPMI_ALG_KDF kdf;      /* the key derivation function */
};
/*@
  predicate correct_tpms_scheme_xor(TPMS_SCHEME_XOR scheme) =
    correct_tpm2_alg_id(scheme.hashAlg)
    && correct_tpm2_alg_id(scheme.kdf);
*/

/* Definition of TPMU_SCHEME_KEYEDHASH Union <INOUT S> */   //1662
typedef union TPMU_SCHEME_KEYEDHASH TPMU_SCHEME_KEYEDHASH;   //TODO struct <--> union
union TPMU_SCHEME_KEYEDHASH {                                //TODO struct <--> union
// typedef struct TPMU_SCHEME_KEYEDHASH TPMU_SCHEME_KEYEDHASH;     //TODO struct <--> union
// struct TPMU_SCHEME_KEYEDHASH {                                  //TODO struct <--> union
    TPMS_SCHEME_HMAC hmac;       /* the signing scheme */
    TPMS_SCHEME_XOR exclusiveOr; /* the obfuscation scheme */
};

/*@
  predicate zero_tpmu_scheme_keyedhash(TPMU_SCHEME_KEYEDHASH tpmu_scheme) =
    (tpmu_scheme.hmac.hashAlg == 0) 
	|| (tpmu_scheme.exclusiveOr.hashAlg == 0 && tpmu_scheme.exclusiveOr.kdf == 0);
*/


/*@
  predicate correct_tpmu_scheme_keyedhash(TPMU_SCHEME_KEYEDHASH tpmu_scheme) =
    correct_tpms_scheme_hash(tpmu_scheme.hmac) 
	|| correct_tpms_scheme_xor(tpmu_scheme.exclusiveOr);
*/

/* Definition of TPMT_KEYEDHASH_SCHEME Structure */     //1675
typedef struct TPMT_KEYEDHASH_SCHEME TPMT_KEYEDHASH_SCHEME;
struct TPMT_KEYEDHASH_SCHEME {
    TPMI_ALG_KEYEDHASH_SCHEME scheme;  /* selects the scheme */
    TPMU_SCHEME_KEYEDHASH details;     /* the scheme parameters */
};


/*@
  predicate zero_tpmt_keyedhash_scheme(TPMT_KEYEDHASH_SCHEME tpmt_scheme) =
    tpmt_scheme.scheme == 0
	&& zero_tpmu_scheme_keyedhash(tpmt_scheme.details);
*/

/*@
  predicate correct_tpmt_keyedhash_scheme(TPMT_KEYEDHASH_SCHEME tpmt_scheme) =
    correct_tpm2_alg_id(tpmt_scheme.scheme)
	&& correct_tpmu_scheme_keyedhash(tpmt_scheme.details);
*/

/* Definition of RSA Types for RSA Signature Schemes */     //1688
typedef TPMS_SCHEME_HASH TPMS_SIG_SCHEME_RSASSA;
typedef TPMS_SCHEME_HASH TPMS_SIG_SCHEME_RSAPSS;


/* Definition of ECC Types for ECC Signature Schemes */
typedef TPMS_SCHEME_HASH  TPMS_SIG_SCHEME_ECDSA;     /* all asymmetric signing schemes */       //1692
typedef TPMS_SCHEME_HASH  TPMS_SIG_SCHEME_SM2;       /* all asymmetric signing schemes */
typedef TPMS_SCHEME_HASH  TPMS_SIG_SCHEME_ECSCHNORR; /* all asymmetric signing schemes */
typedef TPMS_SCHEME_ECDAA TPMS_SIG_SCHEME_ECDAA;     /* schemes that need a hash and a count */ //1695


/* Definition of Types for RSA Encryption Schemes */        //1717
typedef TPMS_SCHEME_HASH TPMS_ENC_SCHEME_OAEP; /* schemes that only need a hash */
typedef TPMS_EMPTY TPMS_ENC_SCHEME_RSAES;      /* schemes that need nothing */


/* Definition of Types for ECC ECC Key Exchange */      //1721
typedef TPMS_SCHEME_HASH TPMS_KEY_SCHEME_ECDH;  /* schemes that need a hash */
typedef TPMS_SCHEME_HASH TPMS_KEY_SCHEME_ECMQV; /* schemes that need a hash */



/* Definition of Types for KDF Schemes */
typedef TPMS_SCHEME_HASH TPMS_SCHEME_MGF1;           /* hash-based key or mask generation functions */
typedef TPMS_SCHEME_HASH TPMS_SCHEME_KDF1_SP800_56A; /* hash-based key or mask generation functions */
typedef TPMS_SCHEME_HASH TPMS_SCHEME_KDF2;           /* hash-based key or mask generation functions */
typedef TPMS_SCHEME_HASH TPMS_SCHEME_KDF1_SP800_108; /* hash-based key or mask generation functions */


/* Definition of TPMU_KDF_SCHEME Union <INOUT S> */         //1731
typedef union TPMU_KDF_SCHEME TPMU_KDF_SCHEME;       //TODO struct <--> union
union TPMU_KDF_SCHEME {                              //TODO struct <--> union
// typedef struct TPMU_KDF_SCHEME TPMU_KDF_SCHEME;         //TODO struct <--> union
// struct TPMU_KDF_SCHEME {                                //TODO struct <--> union
    TPMS_SCHEME_MGF1 mgf1;
    TPMS_SCHEME_KDF1_SP800_56A kdf1_sp800_56a;
    TPMS_SCHEME_KDF2 kdf2;
    TPMS_SCHEME_KDF1_SP800_108 kdf1_sp800_108;
};

/*@
  predicate zero_tpmu_kdf_scheme(TPMU_KDF_SCHEME tpmu_kdf_scheme) =
    tpmu_kdf_scheme.mgf1.hashAlg == 0
    || tpmu_kdf_scheme.kdf1_sp800_56a.hashAlg == 0
    || tpmu_kdf_scheme.kdf2.hashAlg == 0
    || tpmu_kdf_scheme.kdf1_sp800_108.hashAlg == 0;
*/


/*@
  predicate correct_tpmu_kdf_scheme(TPMU_KDF_SCHEME tpmu_kdf_scheme) =
    correct_tpms_scheme_hash(tpmu_kdf_scheme.mgf1)
    || correct_tpms_scheme_hash(tpmu_kdf_scheme.kdf1_sp800_56a)
    || correct_tpms_scheme_hash(tpmu_kdf_scheme.kdf2)
    || correct_tpms_scheme_hash(tpmu_kdf_scheme.kdf1_sp800_108);
*/

/* Definition of TPMT_KDF_SCHEME Structure */           //1749  
typedef struct TPMT_KDF_SCHEME TPMT_KDF_SCHEME;
struct TPMT_KDF_SCHEME {
    TPMI_ALG_KDF scheme;     /* scheme selector */
    TPMU_KDF_SCHEME details; /* scheme parameters */
};


/*@
  predicate zero_tpmt_kdf_scheme(TPMT_KDF_SCHEME tpmt_kdf) =
    tpmt_kdf.scheme == 0
	&& zero_tpmu_kdf_scheme(tpmt_kdf.details);
*/

/*@
  predicate correct_tpmt_kdf_scheme(TPMT_KDF_SCHEME tpmt_kdf) =
    correct_tpm2_alg_id(tpmt_kdf.scheme)
	&& correct_tpmu_kdf_scheme(tpmt_kdf.details);
*/

/* Definition of TPM2_ALG_ID TPMI_ALG_ASYM_SCHEME Type <> */        //1762
typedef TPM2_ALG_ID TPMI_ALG_ASYM_SCHEME;

/* Definition of TPMU_ASYM_SCHEME Union */          //1765
typedef union TPMU_ASYM_SCHEME TPMU_ASYM_SCHEME;     //TODO struct <--> union
union TPMU_ASYM_SCHEME {                             //TODO struct <--> union
// typedef struct TPMU_ASYM_SCHEME TPMU_ASYM_SCHEME;       //TODO struct <--> union
// struct TPMU_ASYM_SCHEME {                               //TODO struct <--> union
    TPMS_KEY_SCHEME_ECDH ecdh;
    TPMS_KEY_SCHEME_ECMQV ecmqv;
    TPMS_SIG_SCHEME_RSASSA rsassa;       /* signing and anonymous signing */
    TPMS_SIG_SCHEME_RSAPSS rsapss;       /* signing and anonymous signing */
    TPMS_SIG_SCHEME_ECDSA ecdsa;         /* signing and anonymous signing */
    TPMS_SIG_SCHEME_ECDAA ecdaa;         /* signing and anonymous signing */
    TPMS_SIG_SCHEME_SM2 sm2;             /* signing and anonymous signing */
    TPMS_SIG_SCHEME_ECSCHNORR ecschnorr; /* signing and anonymous signing */
    TPMS_ENC_SCHEME_RSAES rsaes;         /* schemes with no hash */
    TPMS_ENC_SCHEME_OAEP oaep;           /* schemes with no hash */
    TPMS_SCHEME_HASH anySig;
};

/*@
  predicate zero_tpmu_asym_scheme(TPMU_ASYM_SCHEME tpmu_asym_scheme) =
    tpmu_asym_scheme.ecdh.hashAlg == 0
    || tpmu_asym_scheme.ecmqv.hashAlg == 0
    || tpmu_asym_scheme.rsassa.hashAlg == 0
    || tpmu_asym_scheme.rsapss.hashAlg == 0
    || tpmu_asym_scheme.ecdsa.hashAlg == 0
    || tpmu_asym_scheme.ecdaa.hashAlg == 0
    || tpmu_asym_scheme.ecdaa.count == 0
    || tpmu_asym_scheme.sm2.hashAlg == 0
    || tpmu_asym_scheme.ecschnorr.hashAlg == 0
    || tpmu_asym_scheme.rsaes.empty[0]== (BYTE) 0
    || tpmu_asym_scheme.oaep.hashAlg == 0
    || tpmu_asym_scheme.anySig.hashAlg == 0;
*/



/*@
  predicate correct_tpmu_asym_scheme(TPMU_ASYM_SCHEME tpmu_asym_scheme) =
    correct_tpms_scheme_hash(tpmu_asym_scheme.ecdh)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.ecmqv)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.rsassa)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.rsapss)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.ecdsa)
    || correct_tpms_scheme_ecdaa(tpmu_asym_scheme.ecdaa)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.sm2)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.ecschnorr)
    // || \valid(tpmu_asym_scheme.rsaes.empty + 0) 							//TODO
    || correct_tpms_scheme_hash(tpmu_asym_scheme.oaep)
    || correct_tpms_scheme_hash(tpmu_asym_scheme.anySig);
*/


/* Definition of TPMT_ASYM_SCHEME Structure <> */           //1796
typedef struct TPMT_ASYM_SCHEME TPMT_ASYM_SCHEME;
struct TPMT_ASYM_SCHEME {
    TPMI_ALG_ASYM_SCHEME scheme; /* scheme selector */
    TPMU_ASYM_SCHEME details;    /* scheme parameters */
};

/*@
  predicate zero_tpmt_asym_scheme(TPMT_ASYM_SCHEME tpmt_asym) =
    tpmt_asym.scheme == 0
	&& zero_tpmu_asym_scheme(tpmt_asym.details);
*/

/*@
  predicate correct_tpmt_asym_scheme(TPMT_ASYM_SCHEME tpmt_asym) =
    correct_tpm2_alg_id(tpmt_asym.scheme)
	&& correct_tpmu_asym_scheme(tpmt_asym.details);
*/

/* Definition of TPM2_ALG_ID RSA TPMI_ALG_RSA_SCHEME Type */        //1809
typedef TPM2_ALG_ID TPMI_ALG_RSA_SCHEME;

/* Definition of RSA TPMT_RSA_SCHEME Structure */           //1812
typedef struct TPMT_RSA_SCHEME TPMT_RSA_SCHEME;
struct TPMT_RSA_SCHEME {
    TPMI_ALG_RSA_SCHEME scheme; /* scheme selector */
    TPMU_ASYM_SCHEME details;   /* scheme parameters */
};


/*@
  predicate zero_tpmt_rsa_scheme(TPMT_RSA_SCHEME tpmt_rsa) =
    tpmt_rsa.scheme == 0
	&& zero_tpmu_asym_scheme(tpmt_rsa.details);
*/

/*@
  predicate correct_tpmt_rsa_scheme(TPMT_RSA_SCHEME tpmt_rsa) =
    correct_tpm2_alg_id(tpmt_rsa.scheme)
	&& correct_tpmu_asym_scheme(tpmt_rsa.details);
*/

/* Definition of RSA TPM2B_PUBLIC_KEY_RSA Structure */          //1834
typedef struct TPM2B_PUBLIC_KEY_RSA TPM2B_PUBLIC_KEY_RSA;
struct TPM2B_PUBLIC_KEY_RSA {
    UINT16 size;
    BYTE buffer[TPM2_MAX_RSA_KEY_BYTES];
};

/*@
  predicate zero_tpm2b_public_key_rsa(TPM2B_PUBLIC_KEY_RSA rsa_pub) =
    rsa_pub.size == 0
    // && rsa_pub.buffer[0 .. TPM2_MAX_RSA_KEY_BYTES - 1] == { (BYTE) 0 }
    && \forall int i; 0 <= i  < TPM2_MAX_RSA_KEY_BYTES ==>
        rsa_pub.buffer[i] == (BYTE) 0
    ;
*/

/*@
  predicate valid_tpm2b_public_key_rsa(TPM2B_PUBLIC_KEY_RSA *rsa_pub) =
    \valid(rsa_pub)
    && 0 < rsa_pub->size <= TPM2_MAX_RSA_KEY_BYTES
    && \valid(rsa_pub->buffer + (0 .. (rsa_pub->size - 1)));
*/

/* Definition of RSA TPM2_KEY_BITS TPMI_RSA_KEY_BITS Type */            //1848
typedef TPM2_KEY_BITS TPMI_RSA_KEY_BITS;

/* Definition of ECC TPM2B_ECC_PARAMETER Structure */
typedef struct TPM2B_ECC_PARAMETER TPM2B_ECC_PARAMETER;
struct TPM2B_ECC_PARAMETER {
    UINT16 size;
    BYTE buffer[TPM2_MAX_ECC_KEY_BYTES];
};

/*@
  predicate zero_tpm2b_ecc_parameter(TPM2B_ECC_PARAMETER param) =
    param.size == 0
    // && param.buffer[0 .. TPM2_MAX_ECC_KEY_BYTES - 1] == { (BYTE) 0 }
    && \forall int i; 0 <= i  < TPM2_MAX_ECC_KEY_BYTES ==>
        param.buffer[i] == (BYTE) 0
    ;
*/

/*@
  predicate valid_tpm2b_ecc_param(TPM2B_ECC_PARAMETER *param) =
    \valid(param)
    && 0 < param->size <= TPM2_MAX_ECC_KEY_BYTES
    && \valid(param->buffer + (0 .. (param->size - 1)));
*/

/*@
  predicate valid_read_tpm2b_ecc_param(TPM2B_ECC_PARAMETER *param) =
    \valid_read(param)
	&& 0 < param->size <= TPM2_MAX_ECC_KEY_BYTES
    && \valid_read(param->buffer + (0 .. (param->size - 1)));
*/

/* Definition of ECC TPMS_ECC_POINT Structure */
typedef struct TPMS_ECC_POINT TPMS_ECC_POINT;
struct TPMS_ECC_POINT {
    TPM2B_ECC_PARAMETER x; /* X coordinate */
    TPM2B_ECC_PARAMETER y; /* Y coordinate */
};

/*@
  predicate zero_tpms_ecc_point(TPMS_ECC_POINT ecc_point) =
    zero_tpm2b_ecc_parameter(ecc_point.x)
    && zero_tpm2b_ecc_parameter(ecc_point.y);
*/


/*@
  predicate valid_tpms_ecc_point(TPMS_ECC_POINT *ecc_point) =
    \valid(ecc_point)
    && valid_tpm2b_ecc_param(&ecc_point->x)
    && valid_tpm2b_ecc_param(&ecc_point->y);
*/


/* Definition of TPM2_ALG_ID ECC TPMI_ALG_ECC_SCHEME Type */            //1901
typedef TPM2_ALG_ID TPMI_ALG_ECC_SCHEME;

/* Definition of ECC TPM2_ECC_CURVE TPMI_ECC_CURVE Type */          //1904
typedef TPM2_ECC_CURVE TPMI_ECC_CURVE;

/* Definition of TPMT_SIG_SCHEME ECC TPMT_ECC_SCHEME Structure */       //1908
typedef struct TPMT_ECC_SCHEME TPMT_ECC_SCHEME;
struct TPMT_ECC_SCHEME {
    TPMI_ALG_ECC_SCHEME scheme;   /* scheme selector */
    TPMU_ASYM_SCHEME details;     /* scheme parameters */
};


/*@
  predicate zero_tpmt_ecc_scheme(TPMT_ECC_SCHEME tpmt_ecc) =
    tpmt_ecc.scheme == 0
	&& zero_tpmu_asym_scheme(tpmt_ecc.details);
*/

/*@
  predicate correct_tpmt_ecc_scheme(TPMT_ECC_SCHEME tpmt_ecc) =
    correct_tpm2_alg_id(tpmt_ecc.scheme)
	&& correct_tpmu_asym_scheme(tpmt_ecc.details);
*/

/* Definition of TPMU_ENCRYPTED_SECRET Union <S> */         //1981
typedef union TPMU_ENCRYPTED_SECRET TPMU_ENCRYPTED_SECRET;       //TODO struct <--> union
union TPMU_ENCRYPTED_SECRET {                                    //TODO struct <--> union
// typedef struct TPMU_ENCRYPTED_SECRET TPMU_ENCRYPTED_SECRET;         //TODO struct <--> union
// struct TPMU_ENCRYPTED_SECRET {                                      //TODO struct <--> union
    BYTE ecc[sizeof(TPMS_ECC_POINT)];
    BYTE rsa[TPM2_MAX_RSA_KEY_BYTES];
    BYTE symmetric[sizeof(TPM2B_DIGEST)];
    BYTE keyedHash[sizeof(TPM2B_DIGEST)]; /* Any symmetrically encrypted secret value will be limited to be no larger than a digest. */
};

/* Definition of TPM2B_ENCRYPTED_SECRET Structure */
typedef struct TPM2B_ENCRYPTED_SECRET TPM2B_ENCRYPTED_SECRET;
struct TPM2B_ENCRYPTED_SECRET {
    UINT16 size;
    BYTE secret[sizeof(TPMU_ENCRYPTED_SECRET)];
};

/*@
  predicate zero_tpm2b_encrypted_secret(TPM2B_ENCRYPTED_SECRET tpmb2_enc_secret) =
    tpmb2_enc_secret.size == 0
    // && tpmb2_enc_secret.secret[0 .. sizeof(TPMU_ENCRYPTED_SECRET) - 1] == { (BYTE) 0 }
    && \forall int i; 0 <= i  < sizeof(TPMU_ENCRYPTED_SECRET) ==>
        tpmb2_enc_secret.secret[i] == (BYTE) 0
    ;
*/

/* Definition of TPM2_ALG_ID TPMI_ALG_PUBLIC Type */         //2007
typedef TPM2_ALG_ID TPMI_ALG_PUBLIC;

/* Definition of TPMU_PUBLIC_ID Union <INOUT S> */          //2010
typedef union TPMU_PUBLIC_ID TPMU_PUBLIC_ID;         //TODO struct <--> union
union TPMU_PUBLIC_ID {                               //TODO struct <--> union
// typedef struct TPMU_PUBLIC_ID TPMU_PUBLIC_ID;           //TODO struct <--> union
// struct TPMU_PUBLIC_ID {                                 //TODO struct <--> union
    TPM2B_DIGEST keyedHash;
    TPM2B_DIGEST sym;
    TPM2B_PUBLIC_KEY_RSA rsa;
    TPMS_ECC_POINT ecc;
};


/*@
  predicate zero_tpmu_public_id(TPMU_PUBLIC_ID tpmu_public_id) =
    zero_tpm2b_digest(tpmu_public_id.keyedHash)
    || zero_tpm2b_digest(tpmu_public_id.sym)
    || zero_tpm2b_public_key_rsa(tpmu_public_id.rsa)
    || zero_tpms_ecc_point(tpmu_public_id.ecc);
*/

/*@
  predicate correct_tpmu_public_id(TPMU_PUBLIC_ID *tpmu_public_id) =
    valid_tpm2b_digest(&tpmu_public_id->keyedHash)
    || valid_tpm2b_digest( &tpmu_public_id->sym)
    || valid_tpm2b_public_key_rsa( &tpmu_public_id->rsa)
    || valid_tpms_ecc_point( &tpmu_public_id->ecc);
*/

/* Definition of TPMS_KEYEDHASH_PARMS Structure */          //2027
typedef struct TPMS_KEYEDHASH_PARMS TPMS_KEYEDHASH_PARMS;
struct TPMS_KEYEDHASH_PARMS {
    TPMT_KEYEDHASH_SCHEME scheme; /* Indicates the signing method used for a keyedHash signing object. This field also determines the size of the data field for a data object created with TPM2_Create or TPM2_CreatePrimary. */
};

/*@
  predicate zero_tpms_keyedhash_parms(TPMS_KEYEDHASH_PARMS tpms_params) =
    zero_tpmt_keyedhash_scheme(tpms_params.scheme);
*/

/*@
  predicate correct_tpms_keyedhash_parms(TPMS_KEYEDHASH_PARMS *tpms_params) =
    \valid(tpms_params)
    && correct_tpmt_keyedhash_scheme(tpms_params->scheme);
*/



/* Definition of TPMS_ASYM_PARMS Structure <> */        //2039
typedef struct TPMS_ASYM_PARMS TPMS_ASYM_PARMS;
struct TPMS_ASYM_PARMS {
    TPMT_SYM_DEF_OBJECT symmetric; /* the companion symmetric algorithm for a restricted decryption key and shall be set to a supported symmetric algorithm. This field is optional for keys that are not decryption keys and shall be set to TPM2_ALG_NULL if not used. */
    TPMT_ASYM_SCHEME scheme; /* For a key with the sign attribute SET a valid signing scheme for the key type. For a key with the decrypt attribute SET a valid key exchange protocol. For a key with sign and decrypt attributes shall be TPM2_ALG_NULL */
};

/*@
  predicate zero_tpms_asym_parms(TPMS_ASYM_PARMS tpms_asym_parms) =
    zero_tpmt_sym_def_object(tpms_asym_parms.symmetric)
	&& zero_tpmt_asym_scheme(tpms_asym_parms.scheme);
*/

/*@
  predicate correct_tpms_asym_parms(TPMS_ASYM_PARMS *tpms_asym_parms) =
    \valid(tpms_asym_parms)
    && correct_tpmt_sym_def_object(tpms_asym_parms->symmetric)
	&& correct_tpmt_asym_scheme(tpms_asym_parms->scheme);
*/

/* Definition of RSA TPMS_RSA_PARMS Structure */        //2053
typedef struct TPMS_RSA_PARMS TPMS_RSA_PARMS;
struct TPMS_RSA_PARMS {
    TPMT_SYM_DEF_OBJECT symmetric; /* for a restricted decryption key shall be set to a supported symmetric algorithm key size and mode. if the key is not a restricted decryption key this field shall be set to TPM2_ALG_NULL. */
    TPMT_RSA_SCHEME scheme;        /* scheme. scheme shall before an unrestricted signing key either TPM2_ALG_RSAPSS TPM2_ALG_RSASSA or TPM2_ALG_NULLfor a restricted signing key either TPM2_ALG_RSAPSS or TPM2_ALG_RSASSA for an unrestricted decryption key TPM2_ALG_RSAES TPM2_ALG_OAEP or TPM2_ALG_NULL unless the object also has the sign attribute for a restricted decryption key TPM2_ALG_NULL. NOTE When both sign and decrypt are SET restricted shall be CLEAR and scheme shall be TPM2_ALG_NULL. */
    TPMI_RSA_KEY_BITS keyBits;     /* number of bits in the public modulus */
    UINT32 exponent;               /* the public exponent A prime number greater than 2. When zero indicates that the exponent is the default of 216 + 1 */
};


/*@
  predicate zero_tpms_rsa_parms(TPMS_RSA_PARMS tpms_rsa_parms) =
    zero_tpmt_sym_def_object(tpms_rsa_parms.symmetric)
    && zero_tpmt_rsa_scheme(tpms_rsa_parms.scheme)
	&& tpms_rsa_parms.keyBits == 0
	&& tpms_rsa_parms.exponent == 0;
*/


/*@
  predicate correct_tpms_rsa_parms(TPMS_RSA_PARMS *tpms_rsa_parms) =
    \valid(tpms_rsa_parms)
    && correct_tpmt_sym_def_object(tpms_rsa_parms->symmetric)
    && correct_tpmt_rsa_scheme(tpms_rsa_parms->scheme)
	&& 0 <= tpms_rsa_parms->keyBits < 65536
	&& 0 <= tpms_rsa_parms->exponent < 4294967296;
*/


/* Definition of ECC TPMS_ECC_PARMS Structure */            //2071
typedef struct TPMS_ECC_PARMS TPMS_ECC_PARMS;
struct TPMS_ECC_PARMS {
    TPMT_SYM_DEF_OBJECT symmetric; /* for a restricted decryption key shall be set to a supported symmetric algorithm key size. and mode. if the key is not a restricted decryption key this field shall be set to TPM2_ALG_NULL. */
    TPMT_ECC_SCHEME scheme;        /* If the sign attribute of the key is SET then this shall be a valid signing scheme. NOTE If the sign parameter in curveID indicates a mandatory scheme then this field shall have the same value. If the decrypt attribute of the key is SET then this shall be a valid key exchange scheme or TPM2_ALG_NULL. If the key is a Storage Key then this field shall be TPM2_ALG_NULL. */
    TPMI_ECC_CURVE curveID;        /* ECC curve ID */
    TPMT_KDF_SCHEME kdf;           /* an optional key derivation scheme for generating a symmetric key from a Z value. If the kdf  parameter associated with curveID is not TPM2_ALG_NULL then this is required to be NULL. NOTE There are currently no commands where this parameter has effect and in the reference code this field needs to be set to TPM2_ALG_NULL. */
};


/*@
  predicate zero_tpms_ecc_parms(TPMS_ECC_PARMS tpms_ecc_parms) =
    zero_tpmt_sym_def_object(tpms_ecc_parms.symmetric)
    && zero_tpmt_ecc_scheme(tpms_ecc_parms.scheme)
	&& tpms_ecc_parms.curveID == 0
	&& zero_tpmt_kdf_scheme(tpms_ecc_parms.kdf);
*/

/*@
  predicate correct_tpms_ecc_parms(TPMS_ECC_PARMS *tpms_ecc_parms) =
    \valid(tpms_ecc_parms)
    && correct_tpmt_sym_def_object(tpms_ecc_parms->symmetric)
    && correct_tpmt_ecc_scheme(tpms_ecc_parms->scheme)
	&& 0 <= tpms_ecc_parms->curveID < 65536
	&& correct_tpmt_kdf_scheme(tpms_ecc_parms->kdf);
*/

/* Definition of TPMU_PUBLIC_PARMS Union <INOUT S> */           //2089
typedef union TPMU_PUBLIC_PARMS TPMU_PUBLIC_PARMS;       //TODO struct <--> union
union TPMU_PUBLIC_PARMS {                                //TODO struct <--> union
// typedef struct TPMU_PUBLIC_PARMS TPMU_PUBLIC_PARMS;         //TODO struct <--> union
// struct TPMU_PUBLIC_PARMS {                                  //TODO struct <--> union
    TPMS_KEYEDHASH_PARMS keyedHashDetail; /* sign  decrypt  neither */
    TPMS_SYMCIPHER_PARMS symDetail;       /* a symmetric block cipher */
    TPMS_RSA_PARMS rsaDetail;             /* decrypt + sign2 */
    TPMS_ECC_PARMS eccDetail;             /* decrypt + sign2 */
    TPMS_ASYM_PARMS asymDetail;           /* common scheme structure for RSA and ECC keys */
};

/*@
  predicate zero_tpmu_public_parms(TPMU_PUBLIC_PARMS tpmu_public_parms) =
    zero_tpms_keyedhash_parms( tpmu_public_parms.keyedHashDetail)
    || zero_tpms_symcipher_parms( tpmu_public_parms.symDetail)
    || zero_tpms_rsa_parms( tpmu_public_parms.rsaDetail)
    || zero_tpms_ecc_parms( tpmu_public_parms.eccDetail)
    || zero_tpms_asym_parms( tpmu_public_parms.asymDetail);
*/

/*@
  predicate correct_tpmu_public_parms(TPMU_PUBLIC_PARMS *tpmu_public_parms) =
    correct_tpms_keyedhash_parms( &tpmu_public_parms->keyedHashDetail)
    || correct_tpms_symcipher_parms( &tpmu_public_parms->symDetail)
    || correct_tpms_rsa_parms( &tpmu_public_parms->rsaDetail)
    || correct_tpms_ecc_parms( &tpmu_public_parms->eccDetail)
    || correct_tpms_asym_parms( &tpmu_public_parms->asymDetail);
*/

// TPM2B_PUBLIC

/* Definition of TPMT_PUBLIC Structure */           //2115
typedef struct TPMT_PUBLIC TPMT_PUBLIC;
struct TPMT_PUBLIC {
    TPMI_ALG_PUBLIC type;         /* algorithm associated with this object */
    TPMI_ALG_HASH nameAlg;        /* algorithm used for computing the Name of the object NOTE The + indicates that the instance of a TPMT_PUBLIC may have a + to indicate that the nameAlg may be TPM2_ALG_NULL. */
    TPMA_OBJECT objectAttributes; /* attributes that along with type determine the manipulations of this object */
    TPM2B_DIGEST authPolicy;      /* optional policy for using this key. The policy is computed using the nameAlg of the object. NOTE Shall be the Empty Policy if no authorization policy is present. */
    //TPMU_PUBLIC_PARMS parameters; /* the algorithm or structure details */
    TPMU_PUBLIC_ID unique;        /* the unique identifier of the structure. For an asymmetric key this would be the public key. */
};

/*@
  predicate zero_tpmt_public(TPMT_PUBLIC tpmt_public) =
    tpmt_public.type == 0
    && tpmt_public.nameAlg == 0
    && tpmt_public.objectAttributes == 0
    && zero_tpm2b_digest(tpmt_public.authPolicy)
    //&& zero_tpmu_public_parms(tpmt_public.parameters)
    && zero_tpmu_public_id(tpmt_public.unique);
*/

/*@
  predicate valid_tpmt_public(TPMT_PUBLIC *tpmt_public) =
    \valid(tpmt_public)
    && correct_tpm2_alg_id( tpmt_public->type)
    && correct_tpm2_alg_id( tpmt_public->nameAlg)
    && 0 <= tpmt_public->objectAttributes < 4294967295
    && valid_tpm2b_digest( &tpmt_public->authPolicy)
    //&& correct_tpmu_public_parms(&tpmt_public->parameters)
    && correct_tpmu_public_id(&tpmt_public->unique);
*/

/* Definition of TPM2B_PUBLIC Structure */
typedef struct TPM2B_PUBLIC TPM2B_PUBLIC;
struct TPM2B_PUBLIC {
    UINT16  size;
    TPMT_PUBLIC publicArea; // ok si modif
};

/*@
  predicate zero_tpm2b_public(TPM2B_PUBLIC pub) =
    pub.size == 0
    && zero_tpmt_public(pub.publicArea);
*/

/*@
  predicate valid_tpm2b_public(TPM2B_PUBLIC *pub) =
    \valid(pub)
    && 0 < pub->size <= sizeof(TPMT_PUBLIC)
    && valid_tpmt_public(&pub->publicArea);
*/


/* Definition of UINT32 TPMA_NV Bits */     //2253
typedef uint32_t TPMA_NV;


#define TPMA_NV_PPWRITE        ((TPMA_NV) 0x00000001) /* SET 1 The Index data can be written if Platform Authorization is provided. CLEAR 0 Writing of the Index data cannot be authorized with Platform Authorization. */
#define TPMA_NV_OWNERWRITE     ((TPMA_NV) 0x00000002) /* SET 1 The Index data can be written if Owner Authorization is provided. CLEAR 0 Writing of the Index data cannot be authorized with Owner Authorization. */
#define TPMA_NV_AUTHWRITE      ((TPMA_NV) 0x00000004) /* SET 1 Authorizations to change the Index contents that require USER role may be provided with an HMAC session or password. CLEAR 0 Authorizations to change the Index contents that require USER role may not be provided with an HMAC session or password. */
#define TPMA_NV_POLICYWRITE    ((TPMA_NV) 0x00000008) /* SET 1 Authorizations to change the Index contents that require USER role may be provided with a policy session. CLEAR 0 Authorizations to change the Index contents that require USER role may not be provided with a policy session. NOTE TPM2_NV_ChangeAuth always requires that authorization be provided in a policy session. */
#define TPMA_NV_TPM2_NT_MASK   ((TPMA_NV) 0x000000F0) /* The type of the index. NOTE A TPM is not required to support all TPM2_NT values */
#define TPMA_NV_TPM2_NT_SHIFT  (4)
#define TPMA_NV_RESERVED1_MASK ((TPMA_NV) 0x00000300) /* shall be zero. Reserved for future use */
#define TPMA_NV_POLICY_DELETE  ((TPMA_NV) 0x00000400) /* SET 1 Index may not be deleted unless the authPolicy is satisfied using TPM2_NV_UndefineSpaceSpecial. CLEAR 0 Index may be deleted with proper platform or owner authorization using TPM2_NV_UndefineSpace. */
#define TPMA_NV_WRITELOCKED    ((TPMA_NV) 0x00000800) /* SET 1 Index cannot be written. CLEAR 0 Index can be written. */
#define TPMA_NV_WRITEALL       ((TPMA_NV) 0x00001000) /* SET 1 A partial write of the Index data is not allowed. The write size shall match the defined space size. CLEAR 0 Partial writes are allowed. This setting is required if the .dataSize of the Index is larger than NV_MAX_BUFFER_SIZE for the implementation. */
#define TPMA_NV_WRITEDEFINE    ((TPMA_NV) 0x00002000) /* SET 1 TPM2_NV_WriteLock may be used to prevent further writes to this location. CLEAR 0 TPM2_NV_WriteLock does not block subsequent writes if TPMA_NV_WRITE_STCLEAR is also CLEAR. */
#define TPMA_NV_WRITE_STCLEAR  ((TPMA_NV) 0x00004000) /* SET 1 TPM2_NV_WriteLock may be used to prevent further writes to this location until the next TPM Reset or TPM Restart. CLEAR 0 TPM2_NV_WriteLock does not block subsequent writes if TPMA_NV_WRITEDEFINE is also CLEAR. */
#define TPMA_NV_GLOBALLOCK     ((TPMA_NV) 0x00008000) /* SET 1 If TPM2_NV_GlobalWriteLock is successful then further writes to this location are not permitted until the next TPM Reset or TPM Restart. CLEAR 0 TPM2_NV_GlobalWriteLock has no effect on the writing of the data at this Index. */
#define TPMA_NV_PPREAD         ((TPMA_NV) 0x00010000) /* SET 1 The Index data can be read if Platform Authorization is provided. CLEAR 0 Reading of the Index data cannot be authorized with Platform Authorization. */
#define TPMA_NV_OWNERREAD      ((TPMA_NV) 0x00020000) /* SET 1 The Index data can be read if Owner Authorization is provided. CLEAR 0 Reading of the Index data cannot be authorized with Owner Authorization. */
#define TPMA_NV_AUTHREAD       ((TPMA_NV) 0x00040000) /* SET 1 The Index data may be read if the authValue is provided. CLEAR 0 Reading of the Index data cannot be authorized with the Index authValue. */
#define TPMA_NV_POLICYREAD     ((TPMA_NV) 0x00080000) /* SET 1 The Index data may be read if the authPolicy is satisfied. CLEAR 0 Reading of the Index data cannot be authorized with the Index authPolicy. */
#define TPMA_NV_RESERVED2_MASK ((TPMA_NV) 0x01F00000) /* shall be zero. Reserved for future use */
#define TPMA_NV_NO_DA          ((TPMA_NV) 0x02000000) /* SET 1 Authorization failures of the Index do not affect the DA logic and authorization of the Index is not blocked when the TPM is in Lockout mode. CLEAR 0 Authorization failures of the Index will increment the authorization failure counter and authorizations of this Index are not allowed when the TPM is in Lockout mode. */
#define TPMA_NV_ORDERLY        ((TPMA_NV) 0x04000000) /* SET 1 NV Index state is only required to be saved when the TPM performs an orderly shutdown TPM2_Shutdown. CLEAR 0 NV Index state is required to be persistent after the command to update the Index completes successfully, that is, the NV update is synchronous with the update command. */
#define TPMA_NV_CLEAR_STCLEAR  ((TPMA_NV) 0x08000000) /* SET 1 TPMA_NV_WRITTEN for the Index is CLEAR by TPM Reset or TPM Restart. CLEAR 0 TPMA_NV_WRITTEN is not changed by TPM Restart. NOTE 1    This attribute may only be SET if TPM2_NT is not TPM2_NT_COUNTER. NOTE 2    If the TPMA_NV_ORDERLY is SET TPMA_NV_WRITTEN will be CLEAR by TPM Reset. */
#define TPMA_NV_READLOCKED     ((TPMA_NV) 0x10000000) /* SET 1 Reads of the Index are blocked until the next TPM Reset or TPM Restart. CLEAR 0 Reads of the Index are allowed if proper authorization is provided. */
#define TPMA_NV_WRITTEN        ((TPMA_NV) 0x20000000) /* SET 1 Index has been written. CLEAR 0 Index has not been written. */
#define TPMA_NV_PLATFORMCREATE ((TPMA_NV) 0x40000000) /* SET 1 This Index may be undefined with Platform Authorization but not with Owner Authorization. CLEAR 0 This Index may be undefined using Owner Authorization but not with Platform Authorization. The TPM will validate that this attribute is SET when the Index is defined using Platform Authorization and will validate that this attribute is CLEAR when the Index is defined using Owner Authorization. */
#define TPMA_NV_READ_STCLEAR   ((TPMA_NV) 0x80000000) /* SET 1 TPM2_NV_ReadLock may be used to SET TPMA_NV_READLOCKED for this Index. CLEAR 0 TPM2_NV_ReadLock has no effect on this Index. */


/*@
  predicate	correct_tpma_nv(TPMA_NV tpma_nv) =
    tpma_nv \in 
      {
        TPMA_NV_PPWRITE, TPMA_NV_OWNERWRITE, TPMA_NV_AUTHWRITE, TPMA_NV_POLICYWRITE, 
        TPMA_NV_TPM2_NT_MASK, TPMA_NV_TPM2_NT_SHIFT, TPMA_NV_RESERVED1_MASK, TPMA_NV_POLICY_DELETE,
        TPMA_NV_WRITELOCKED, TPMA_NV_WRITEALL, TPMA_NV_WRITEDEFINE, TPMA_NV_WRITE_STCLEAR,
        TPMA_NV_GLOBALLOCK, TPMA_NV_PPREAD, TPMA_NV_OWNERREAD, TPMA_NV_AUTHREAD, 
        TPMA_NV_POLICYREAD, TPMA_NV_RESERVED2_MASK, TPMA_NV_NO_DA, TPMA_NV_ORDERLY, 
        TPMA_NV_CLEAR_STCLEAR, TPMA_NV_READLOCKED, TPMA_NV_WRITTEN, TPMA_NV_PLATFORMCREATE, 
        TPMA_NV_READ_STCLEAR
      }
	;
*/

/*@
  predicate	valid_tpma_nv(TPMA_NV * tpma_nv) =
    \valid(tpma_nv)
	&& correct_tpma_nv(*tpma_nv)
    ;
*/


/* Definition of TPMS_NV_PUBLIC Structure */        //2305
typedef struct TPMS_NV_PUBLIC TPMS_NV_PUBLIC;
struct TPMS_NV_PUBLIC {
    TPMI_RH_NV_INDEX nvIndex; /* the handle of the data area */
    TPMI_ALG_HASH nameAlg;    /* hash algorithm used to compute the name of the Index and used for the authPolicy.  For an extend index the hash algorithm used for the extend. */
    TPMA_NV attributes;       /* the Index attributes */
    TPM2B_DIGEST authPolicy;  /* optional access policy for the Index. The policy is computed using the nameAlg . NOTE: this shall be the Empty Policy if no authorization policy is present. */
    UINT16 dataSize;          /* the size of the data area. The maximum size is implementation dependent. The minimum maximum size is platform-specific. */
};

/*@
  predicate zero_tpms_nv_public(TPMS_NV_PUBLIC tpms_nv_public) =
	tpms_nv_public.nvIndex == 0
	&& tpms_nv_public.nameAlg == 0
	&& tpms_nv_public.attributes == 0
	&& zero_tpm2b_digest(tpms_nv_public.authPolicy)
	&& tpms_nv_public.dataSize== 0
	;
*/

/*@
  predicate valid_tpms_nv_public(TPMS_NV_PUBLIC *tpms_nv_public) =
    \valid(tpms_nv_public)
	// TODO nvIndex condition (handle) ??
	&& valid_tpm2_alg_id(&tpms_nv_public->nameAlg)
	&& valid_tpma_nv(&tpms_nv_public->attributes)
	&& valid_tpm2b_digest(&tpms_nv_public->authPolicy)
	// TODO condition ?? 
	;
*/

/* Definition of TPM2B_NV_PUBLIC Structure */           //2326
typedef struct TPM2B_NV_PUBLIC TPM2B_NV_PUBLIC;
struct TPM2B_NV_PUBLIC {
    UINT16  size;
    TPMS_NV_PUBLIC nvPublic;
};

/*@
  predicate zero_tpm2b_nv_public(TPM2B_NV_PUBLIC tpm2b_nv_public) =
    tpm2b_nv_public.size == 0
	&& zero_tpms_nv_public(tpm2b_nv_public.nvPublic)
	;
*/

/*@
  predicate valid_tpm2b_nv_public(TPM2B_NV_PUBLIC *tpm2b_nv_public) =
    \valid(tpm2b_nv_public)
	&& 0 <= tpm2b_nv_public->size 		// TODO upper bound ?
	&& valid_tpms_nv_public(&tpm2b_nv_public->nvPublic)
	;
*/