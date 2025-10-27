struct __struct_bit {
    unsigned char b0 : 1 ;
    unsigned char b1 : 1 ;
    unsigned char b2 : 1 ;
    unsigned char b3 : 1 ;
    unsigned char b4 : 1 ;
    unsigned char b5 : 1 ;
    unsigned char b6 : 1 ;
    unsigned char b7 : 1 ;
};

struct __struct_bit flags;

/*@
    assigns flags.b0;
    ensures G: flags.b0 == (v & 1);
*/
int set_b0(unsigned char v){
    flags.b0 = v;
    return 0;
}