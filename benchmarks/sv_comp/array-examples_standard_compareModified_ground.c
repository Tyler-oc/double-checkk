
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

/*@ assigns \nothing; */
extern void abort(void);

/*@ assigns \nothing; */
extern void __VERIFIER_error(void);

/*@ assigns \nothing; */
extern void __VERIFIER_assume(int);

/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);

/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);

/*@ assigns \nothing; */
extern long __VERIFIER_nondet_long(void);

/*@ assigns \nothing; */
extern unsigned long __VERIFIER_nondet_ulong(void);

/*@ assigns \nothing; */
extern short __VERIFIER_nondet_short(void);

/*@ assigns \nothing; */
extern unsigned short __VERIFIER_nondet_ushort(void);

/*@ assigns \nothing; */
extern char __VERIFIER_nondet_char(void);

/*@ assigns \nothing; */
extern unsigned char __VERIFIER_nondet_uchar(void);

/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool(void);

/*@ requires \true; assigns \nothing; */
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
        ERROR: __VERIFIER_error();
    }
}
#define SIZE 100000

int main( ) {
  int a[SIZE];
  int b[SIZE];
  int i = 0;
  int c [SIZE];
  int rv = 1;
	
	for (int j = 0; j < SIZE ; j++ ) {
    a[j] = __VERIFIER_nondet_int();
		b[j] = __VERIFIER_nondet_int();
  }
	
  while ( i < SIZE ) {
    if ( a[i] != b[i] ) {
      rv = 0;
    }
    c[i] = a[i];
    i = i+1;
  }
  
  int x;
  if ( rv ) {
    for ( x = 0 ; x < SIZE ; x++ ) {
      __VERIFIER_assert(  a[x] == b[x]  );
    }
  }
  
  for ( x = 0 ; x < SIZE ; x++ ) {
    __VERIFIER_assert(  a[x] == c[x]  );
  }
  return 0;
}