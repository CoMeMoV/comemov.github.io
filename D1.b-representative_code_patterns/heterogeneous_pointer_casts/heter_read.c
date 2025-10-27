typedef unsigned char u8;
typedef unsigned short u16;

u8 array[2] ;
/*@
    requires \valid(array+(0..1));
    assigns array[0..1];
    ensures G: \result == v;
*/
u16 read_value(u16 v){
	array[0] = v & 0xff;
	array[1] = (v>>8) & 0xff;
	return ((u16*)array)[0];
}