typedef unsigned char u8;
typedef unsigned short u16;

u8 array[2] ;
/*@
    requires \valid(array+(0..1));
    assigns array[0..1];
    ensures G: *(u16*)array == v;
*/
u16 write_value(u16 v){
	*(u16*)array = v;
	return 0;
}