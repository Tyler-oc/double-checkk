
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
#define N 100000

int main( ) {
  int a1[N];
  int a2[N];

  int a;
  for ( a = 0 ; a < N ; a++ ) {
      a1[a] = __VERIFIER_nondet_int();
  }

  int i;
  for ( i = 0 ; i < N ; i++ ) {
    a2[i] = a1[i];
  }
  
  int x;
  for ( x = 0 ; x < N ; x++ ) {
    __VERIFIER_assert(  a1[x] == a2[x]  );
  }
  return 0;
}