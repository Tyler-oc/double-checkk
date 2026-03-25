
#include <stddef.h>
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern _Bool __VERIFIER_nondet_bool(void);
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } }

extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

#define SIZE 100000

int main( ) {
  int a[SIZE];
  int b[SIZE];
	
	for (int j = 0; j < SIZE ; j++ ) {
    a[j] = __VERIFIER_nondet_int();
		b[j] = __VERIFIER_nondet_int();
  }

  int i = 0;
  int rv = 1;
  while ( i < SIZE ) {
    if ( a[i] != b[i] ) {
      rv = 0;
    }
    i = i+1;
  }
  
  if ( rv ) {
    int x;
    for ( x = 0 ; x < SIZE ; x++ ) {
      __VERIFIER_assert(  a[x] == b[x]  );
    }
  }
  return 0;
}