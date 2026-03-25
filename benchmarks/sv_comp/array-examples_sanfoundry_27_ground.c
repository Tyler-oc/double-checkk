
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

/*
 * Adapted from http://www.sanfoundry.com/c-programming-examples-arrays/
 * C Program to Find the Largest Number in an Array
 */
#define SIZE 100000

int main()
{
    int array[SIZE];
    int i;
			
		for(i = 0; i < SIZE; i++) 
		{
		  array[i] = __VERIFIER_nondet_int();
		}
		
    int largest = array[0];
    for (i = 1; i < SIZE; i++)
    {
        if (largest < array[i])
            largest = array[i];
    }
    
    int x;
    for ( x = 0 ; x < SIZE ; x++ ) {
      __VERIFIER_assert(  largest >= array[ x ]  );
    }
    
    return 0;
}