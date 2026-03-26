
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
/*
 * Adapted from http://www.sanfoundry.com/c-programming-examples-arrays/
 * C Program to Print the Number of Odd & Even Numbers in an Array
 */
#define SIZE 100000

void printEven( int i ) {
  __VERIFIER_assert(  ( i % 2 ) == 0  );
  // printf( "%d" , i );
}

void printOdd( int i ) {
  __VERIFIER_assert(  ( i % 2 ) != 0  );
  // printf( "%d" , i );
}

int main()
{
    int array[SIZE];
    int i;
    int num = __VERIFIER_nondet_int();
		
		for(i = 0; i < num; i++) 
		{
		  array[i] = __VERIFIER_nondet_int();
		}
 
    //printf("Even numbers in the array are - ");
    for (i = 0; i < num; i++) // use of uninitialized num
    {
        if (array[i] % 2 == 0)
        {
            printEven( array[i] );
        }
    }
    //printf("\n Odd numbers in the array are -");
    for (i = 0; i < num; i++)
    {
        if (array[i] % 2 != 0)
        {
            printOdd( array[i] );
        }
    }
  return 0;
}