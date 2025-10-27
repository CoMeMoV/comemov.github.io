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

union __union_flags
{
    struct __struct_bit bit;
    unsigned char byte;
};

union __union_flags flag;

/*@
    assigns flag;
    ensures flag.bit.b0 == v % 2;
    ensures G: flag.bit.b1 == (v>>1) % 2;
    //...
*/
int set_byte(unsigned char v){
    flag.byte = v;
    return 0;
}