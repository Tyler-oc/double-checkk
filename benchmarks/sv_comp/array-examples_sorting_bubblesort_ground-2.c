
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

#define N 100000

int main( ) {
  int a[ N ];
	
	for(int j = 0; j < N; j++)
	{
	  a[j] = __VERIFIER_nondet_int();
	}
	
  int swapped = 1;
  while ( swapped ) {
    swapped = 0;
    int i = 1;
    while ( i < N ) {
      if ( a[i - 1] < a[i] ) {
        int t = a[i];
        a[i] = a[i - 1];
        a[i-1] = t;
        swapped = 1;
      }
      i = i + 1;
    }
  }

  int x;
  int y;
  for ( x = 0 ; x < N ; x++ ) {
    for ( y = x+1 ; y < N ; y++ ) {
      __VERIFIER_assert(  a[x] <= a[y]  );
    }
  }
  return 0;
}