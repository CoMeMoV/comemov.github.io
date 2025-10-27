/* Command to run the proof with Frama-C:
 frama-c-gui -c11 byte_level.c -wp -wp-rte -wp-timeout 30 -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce,script -wp-smoke-tests -wp-prop="-@lemma"

or, with Typed+cast :
 frama-c-gui -c11 byte_level.c -wp -wp-rte -wp-timeout 30 -wp-time-extra 8 -wp-prover altergo,cvc4,cvc4-ce,script -wp-smoke-tests -wp-prop="-@lemma"  -wp-model Typed+cast
*/

#include <stdint.h>       // for uint types definitions
#include <string.h>       // for size_t definition
#include <byteswap.h>     // used in marshal
#define HOST_TO_BE_32(value) __bswap_32 (value) // swap endianness

/*@
  requires \valid(offset) && 0 <= *offset <= UINT8_MAX - sizeof(in);
  requires buff_size > 0 && \valid(&buff[0] + (0 .. buff_size - 1));
  requires *offset <= buff_size && sizeof(in) + *offset <= buff_size;
  requires \separated(offset, buff);
  
  assigns *offset, (&buff[*offset])[0..sizeof(in) - 1];

  ensures *offset ==  \old(*offset) + sizeof(in);    
  ensures \result == 0;
*/
int uint32_Marshal(uint32_t in,uint8_t buff[],size_t buff_size,size_t *offset){ 
  size_t  local_offset = 0; 
  if (offset != NULL){local_offset = *offset;}
  in = HOST_TO_BE_32(in); 
  memcpy(&buff[local_offset], &in, sizeof (in)); 
  if (offset != NULL){*offset = local_offset + sizeof (in);} 
  return 0; 
}
