/* Command to run the proof with Frama-C:
 frama-c-gui -c11 struct_union.c -wp -wp-rte -wp-timeout 30 -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce -wp-smoke-tests -wp-prop="-@lemma"
*/

#include <stdio.h>     //TODO
#include <stdlib.h>     //TODO

#include <stdint.h>       // for uint types definitions
#include <string.h>       // for size_t definition
#include "./tpm2_types.h"
#include <byteswap.h>     // used in marshal
#define HOST_TO_BE_32(value) __bswap_32 (value) // swap endianness



/* Definition of TPMT_SYM_DEF Structure */
typedef struct TPMT_SYM_DEF TPMT_SYM_DEF;
struct TPMT_SYM_DEF {
    TPMI_ALG_SYM algorithm;    /* indicates a symmetric algorithm */
    TPMU_SYM_KEY_BITS keyBits; /* a supported key size */
    TPMU_SYM_MODE mode;        /* the mode for the key */
};


/*@
  predicate zero_tpmt_sym_def(TPMT_SYM_DEF tpmt_obj) =
    tpmt_obj.algorithm == 0
	&& zero_tpmu_sym_key_bits(tpmt_obj.keyBits)
	&& zero_tpmu_sym_mode(tpmt_obj.mode);
*/


/** Type for representing TPM-Session
 */
typedef struct {
    TPM2B_NAME                         bound_entity;    /**< Entity to which the session  
                                                            is bound */
    TPM2B_ENCRYPTED_SECRET            encryptedSalt;    /**< Encrypted salt which can 
                                                            be provided by application */
            // = Digest-like
    TPM2B_DATA                                 salt;    /**< Salt computed if no encrypted 
                                                             salt is provided */
            // = Digest-like
            
    TPMT_SYM_DEF                          symmetric;    /**< Algorithm selection for  
                                                            parameter encryption */
    TPMI_ALG_HASH                          authHash;    /**< Hashalg used for authorization */
            // uint16_t
    TPM2B_DIGEST                         sessionKey;    /**< sessionKey used for KDFa  
                                                            to compute symKey */
    TPM2_SE                             sessionType;    /**< Type of the session  
                                                            (HMAC, Policy) */
            // uint8_t
    TPMA_SESSION                  sessionAttributes;    /**< Flags which define the  
                                                            session behaviour */
            // uint8_t
    TPMA_SESSION              origSessionAttributes;    /**< Copy of flags which define  
                                                            the session behaviour */
            // uint8_t
    TPM2B_NONCE                         nonceCaller;    /**< Nonce computed by the ESAPI  
                                                            for every session call */
    TPM2B_NONCE                            nonceTPM;    /**< Nonce which is returned by the  
                                                            TPM for every session call */
    IESYSC_PARAM_ENCRYPT                    encrypt;    /**< Indicate parameter encryption  
                                                            by the TPM */
            // uint8_t, values in {0,1}
    IESYSC_PARAM_DECRYPT                    decrypt;    /**< Indicate parameter decryption  
                                                            by the TPM */
            // uint8_t, values in {0,1}
    IESYSC_TYPE_POLICY_AUTH     type_policy_session;    /**< Field to store markers for  
                                                            policy sessions */
            // uint8_t, values in {0,1,2}
    UINT16                         sizeSessionValue;    /**< Size of sessionKey plus  
                                                            optionally authValue */
    BYTE           sessionValue [2*sizeof(TPMU_HA)];    /**< sessionKey || AuthValue */
            // uint8_t[number]
    UINT16                            sizeHmacValue;    /**< Size of sessionKey plus  
                                                            optionally authValue */
} IESYS_SESSION;

/*@
  predicate zero_iesys_session(IESYS_SESSION session) =
	zero_tpm2b_name(session.bound_entity)
	&& zero_tpm2b_encrypted_secret(session.encryptedSalt)
	&& zero_tpm2b_data(session.salt)
	&& zero_tpmt_sym_def(session.symmetric)
	&& session.authHash == 0
	&& zero_tpm2b_digest(session.sessionKey)
	&& session.sessionType == 0
	&& session.sessionAttributes == 0
	&& session.origSessionAttributes == 0
	&& zero_tpm2b_digest(session.nonceCaller)
	&& zero_tpm2b_digest(session.nonceTPM)
	&& session.encrypt == 0
	&& session.decrypt == 0
	&& session.type_policy_session == 0
	&& session.sizeSessionValue == 0
	&& session.sessionValue[0 .. 2 * sizeof(TPMU_HA) - 1] == { (BYTE) 0 }
	&& session.sizeHmacValue == 0
	;
*/

/** Type for representing public info of a TPM-Resource
 */
// The 4 fail together, but any combination of 3 succeeds in less than 5min
typedef union {        // ./src/tss2-esys/esys_type.h
    //TPM2B_PUBLIC                rsrc_key_pub; // ok si modif   /**< Public info for key objects */
    //TPM2B_NV_PUBLIC              rsrc_nv_pub; //ok - no modif    /**< Public info for NV ram objects */
    //IESYS_SESSION               rsrc_session;   //Ok  /**< Internal esapi session information */
    TPMS_EMPTY                    rsrc_empty; //ok   /**< no specialized date for resource */
} IESYS_RSRC_UNION;

// /*@
//   predicate zero_iesys_rsrc_union(IESYS_RSRC_UNION rsrc_union) =
// 	zero_tpm2b_public(rsrc_union.rsrc_key_pub)
// 	|| zero_tpm2b_nv_public(rsrc_union.rsrc_nv_pub)
// 	|| zero_iesys_session(rsrc_union.rsrc_session)
// 	|| rsrc_union.rsrc_empty.empty[0]== {(BYTE) 0};
// */

typedef struct {        // ./src/tss2-esys/esys_type.h
    TPM2_HANDLE                       handle;    /**< Handle used by TPM */
    TPM2B_NAME                          name;    /**< TPM name of the object */
    IESYSC_RESOURCE_TYPE            rsrcType;    /**< Selector for resource type */
    IESYS_RSRC_UNION                    misc; //complex   /**< Resource specific information */
} IESYS_RESOURCE;

/*@
  predicate zero_iesys_resource(IESYS_RESOURCE rsrc) =
	rsrc.handle == 0
	&& zero_tpm2b_name(rsrc.name)
	&& rsrc.rsrcType == 0;
*/

typedef struct NODE_T {
  uint32_t      handle;   // the handle used as reference
  IESYS_RESOURCE      rsrc;     // the metadata for this rsrc
  struct NODE_T *   next; // next node in the list
} NODE_T; // linked list of resource


/* @
  predicate zero_tpm2b_name(TPM2B_NAME tpm2b_name) =
    tpm2b_name.size == 0 && \forall int i; 0 <= i  < 68 ==> tpm2b_name.name[i] == 0;
  predicate zero_resource(RESOURCE rsrc) =
    rsrc.handle == 0 && zero_tpm2b_name(rsrc.name) && rsrc.rsrcType == 0;
  predicate zero_rsrc_node_t(NODE_T node) =
    node.handle == 0 && zero_resource(node.rsrc) && node.next == \null;
*/

/*@
  predicate zero_rsrc_node_t(NODE_T node) =
	node.handle == 0
	&& zero_iesys_resource(node.rsrc)
	&& node.next == \null;
*/
/************** Logic lists and linked lists definitions *************/
/*@
  predicate ptr_sep_from_list{L}(NODE_T* e, \list<NODE_T*> ll) =
    \forall integer n; 0 <= n < \length(ll) ==> \separated(e, \nth(ll, n));
  predicate dptr_sep_from_list{L}(NODE_T** e, \list<NODE_T*> ll) =
    \forall integer n; 0 <= n < \length(ll) ==> \separated(e, \nth(ll, n));
  predicate in_list{L}(NODE_T* e, \list<NODE_T*> ll) =
    \exists integer n; 0 <= n < \length(ll) && \nth(ll, n) == e;
  // predicate in_list_handle{L}(uint32_t out_handle, \list<NODE_T*> ll) =
  //   \exists integer n; 0 <= n < \length(ll) && \nth(ll, n)->handle == out_handle;
  inductive linked_ll{L}(NODE_T *bl, NODE_T *el, \list<NODE_T*> ll) {
    case linked_ll_nil{L}: \forall NODE_T *el; linked_ll{L}(el, el, \Nil);
    case linked_ll_cons{L}: \forall NODE_T *bl, *el, \list<NODE_T*> tail;
      (\separated(bl, el) && \valid(bl) && linked_ll{L}(bl->next, el, tail) &&
      ptr_sep_from_list(bl, tail)) ==>
        linked_ll{L}(bl, el, \Cons(bl, tail));
  }
  predicate unchanged_ll{L1, L2}(\list<NODE_T*> ll) =
    \forall integer n; 0 <= n < \length(ll) ==>
      \valid{L1}(\nth(ll,n)) && \valid{L2}(\nth(ll,n)) &&
      \at((\nth(ll,n))->next, L1) == \at((\nth(ll,n))->next, L2);
  predicate all_sep_in_list(\list<NODE_T*> ll) =
    \forall integer n1, n2; (0 <= n1 < \length(ll) && 0 <= n2 < \length(ll) && n1 != n2) ==>
        \separated(\nth(ll, n1), \nth(ll, n2));
  axiomatic Node_To_ll {
    logic \list<NODE_T*> to_ll{L}(NODE_T* beg, NODE_T* end) 
      reads {node->next | NODE_T* node; \valid(node) &&
                           in_list(node, to_ll(beg, end))};
    axiom to_ll_nil{L}: \forall NODE_T *node; to_ll{L}(node, node) == \Nil;
    axiom to_ll_cons{L}: \forall NODE_T *beg, *end;
      (\separated(beg, end) && \valid{L}(beg) &&
      ptr_sep_from_list{L}(beg, to_ll{L}(beg->next, end))) ==>
        to_ll{L}(beg, end) == \Cons(beg, to_ll{L}(beg->next, end));
  }
*/

#define _rsrc_alloc_max 100
static NODE_T _rsrc_bank[_rsrc_alloc_max];  // bank used by the static allocator
static int _rsrc_alloc_idx = 0;  // index of the next rsrc node to be allocated 

/*@ 
  predicate valid_rsrc_mem_bank{L} = 0 <= _rsrc_alloc_idx <= _rsrc_alloc_max;
*/


#define _int_alloc_max 100
static int _int_bank[_int_alloc_max]; 
static int _int_alloc_idx = 0; 
/*@ 
  predicate valid_int_mem_bank{L} = 0 <= _int_alloc_idx <= _int_alloc_max;
*/

/***************************************************************************/

/*@
  requires valid_int_mem_bank;
  assigns _int_alloc_idx, _int_bank[\old(_int_alloc_idx)];
  assigns \result \from _int_bank[\old(_int_alloc_idx)];
  ensures valid_int_mem_bank; 
  
  behavior not_allocable:
    assumes _int_alloc_idx == _int_alloc_max;
    
    ensures _int_alloc_idx == _int_alloc_max;
    ensures \result == NULL;
    ensures _int_bank == \old(_int_bank);
    ensures \forall int i; 0 <= i < _int_alloc_max ==> 
              _int_bank[i] == \old(_int_bank[i]); 
  behavior allocable:
    assumes 0 <= _int_alloc_idx < _int_alloc_max;
    
    ensures _int_alloc_idx == \old(_int_alloc_idx) + 1;
    ensures \result == &(_int_bank[ _int_alloc_idx - 1]);
    ensures \valid(\result);
    ensures \forall int i; 0 <= i < _int_alloc_max && i != \old(_int_alloc_idx) ==> 
            _int_bank[i] == \old(_int_bank[i]);  //proved
  disjoint behaviors; complete behaviors;
*/
int *calloc_int()
{
  if(_int_alloc_idx < _int_alloc_max) {
    _int_bank[_int_alloc_idx] = (int) 0;
    _int_alloc_idx += 1;
    return &_int_bank[_int_alloc_idx - 1];
  }
  return NULL;
}

/*@
  assigns _rsrc_bank[0];
  ensures \forall int i; 0 < i < _rsrc_alloc_max ==> 
          _rsrc_bank[i] == \old(_rsrc_bank[i]);  
            //difficult to prove without script
*/
NODE_T *my_calloc_NODE_T()
{
  static const IESYS_RESOURCE empty_RESOURCE;
  _rsrc_bank[0].handle = (uint32_t) 0;
  _rsrc_bank[0].rsrc = empty_RESOURCE;
  _rsrc_bank[0].next = NULL;
  return 0;

}

/*@
  requires valid_rsrc_mem_bank;
  assigns _rsrc_alloc_idx, _rsrc_bank[\old(_rsrc_alloc_idx)];
  assigns \result \from _rsrc_bank[\old(_rsrc_alloc_idx)];
  ensures valid_rsrc_mem_bank; 
  
  behavior not_allocable:
    assumes _rsrc_alloc_idx == _rsrc_alloc_max;
    
    ensures _rsrc_alloc_idx == _rsrc_alloc_max;
    ensures \result == NULL;
    ensures _rsrc_bank == \old(_rsrc_bank);
    ensures \forall int i; 0 <= i < _rsrc_alloc_max ==> 
              _rsrc_bank[i] == \old(_rsrc_bank[i]); 
  behavior allocable:
    assumes 0 <= _rsrc_alloc_idx < _rsrc_alloc_max;
    
    ensures _rsrc_alloc_idx == \old(_rsrc_alloc_idx) + 1;
    ensures \result == &(_rsrc_bank[ _rsrc_alloc_idx - 1]);
    ensures \valid(\result);
    ensures zero_rsrc_node_t( *(\result) );
    ensures Po: \forall int i; 0 <= i < _rsrc_alloc_max && i != \old(_rsrc_alloc_idx) ==> 
            _rsrc_bank[i] == \old(_rsrc_bank[i]);  
              //difficult to prove without script
  disjoint behaviors; complete behaviors;
*/
NODE_T *calloc_NODE_T()
{
  static const IESYS_RESOURCE empty_RESOURCE;
  if(_rsrc_alloc_idx < _rsrc_alloc_max) {
    _rsrc_bank[_rsrc_alloc_idx].handle = (uint32_t) 0;
    _rsrc_bank[_rsrc_alloc_idx].rsrc = empty_RESOURCE;
    _rsrc_bank[_rsrc_alloc_idx].next = NULL;
    _rsrc_alloc_idx += 1;
    return &_rsrc_bank[_rsrc_alloc_idx - 1];
  }
  return NULL;
}


/* Command to run the proof with Frama-C:
frama-c-gui -c11 example.c -wp -wp-rte -wp-prover altergo,cvc4,cvc4-ce,script 
-wp-timeout 50 -wp-smoke-tests -wp-prop="-@lemma"
*/


/**
frama-c-gui -c11 struct_union.c -wp -wp-rte -wp-fct-timeout "createNode:180, getNode:240, iesys_handle_to_tpm_handle:60" -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce -wp-par x -wp-smoke-tests -wp-fct="createNode, getNode" -wp-model Typed+cast -wp-prop="-@lemma"
*/
/**
frama-c-gui -c11 struct_union.c -wp -wp-rte -wp-fct-timeout "calloc_NODE_T:10, createNode:60, getNode:60, iesys_handle_to_tpm_handle:60, uint32_Marshal:100" -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce -wp-cache update -wp-par x -wp-smoke-tests -wp-fct="calloc_NODE_T, createNode, getNode, iesys_handle_to_tpm_handle, uint32_Marshal" -wp-model Typed+cast -wp-prop="-@lemma"
*/
