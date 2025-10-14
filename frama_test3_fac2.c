#include <stdio.h>

/*@
  logic integer factorial(integer n) =
    (n <= 0) ? 1 : n * factorial(n - 1);
*/

/*@
  assigns \nothing;
  ensures \result == factorial(5);
*/
int main()
{
  int s, r, n = 5, u, v;

  /* keep an explicit runtime/verification check for n bounds */
  /*@ assert 0 <= n <= 12; */

  /* Outer loop:
     - r runs from 1 up to n-1,
     - u == factorial(r) at loop head
  */
  /*@
    loop invariant 1 <= r <= n;
    loop invariant u == factorial(r);
    loop assigns r, s, u, v;
    loop variant n - r;
  */
  for (u = r = 1; r < n; r++) {
    v = u;

    /* Inner loop rewritten as a simple counting loop: u += v executed r times */
    /*@
      loop invariant 0 <= s <= r;
      loop invariant u == v * (s + 1);
      loop assigns s, u;
      loop variant r - s;
    */
    for (s = 0; s < r; ++s) {
      u += v;
    }

    /* now u == v * (r + 1) == factorial(r+1) */
    /*@ assert u == factorial(r + 1); */
  }

  return u;
}

//3 messages total (GPT-5 Thinking), works with z3 and cvc5 solvers