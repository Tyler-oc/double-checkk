/*@
  logic integer factorial(integer n) =
    (n <= 0) ? 1 : n * factorial(n - 1);
*/

/*@
  requires n >= 0;
  requires n <= 12;
  assigns \nothing;
  ensures \result == factorial(n);
*/
int compute_factorial(int n) {
    int i, f;
    
    f = 1;
    /*@
      loop invariant 1 <= i <= n + 1;
      loop invariant f == factorial(i - 1);
      loop invariant f >= 1;
      loop invariant 1 <= i <= 13;
      loop invariant i == 1 ==> f == 1;
      loop invariant i == 2 ==> f == 1;
      loop invariant i == 3 ==> f == 2;
      loop invariant i == 4 ==> f == 6;
      loop invariant i == 5 ==> f == 24;
      loop invariant i == 6 ==> f == 120;
      loop invariant i == 7 ==> f == 720;
      loop invariant i == 8 ==> f == 5040;
      loop invariant i == 9 ==> f == 40320;
      loop invariant i == 10 ==> f == 362880;
      loop invariant i == 11 ==> f == 3628800;
      loop invariant i == 12 ==> f == 39916800;
      loop invariant i == 13 ==> f == 479001600;
      loop assigns i, f;
      loop variant n - i + 1;
    */
    for (i = 1; i <= n; i++)
        f = f * i;
    
    return f;
}

/*@
  assigns \nothing;
*/
int main()
{
    int n = 5, i, f;

    f = 1;
    /*@
      loop invariant 1 <= i <= n + 1;
      loop invariant f == factorial(i - 1);
      loop invariant f >= 1;
      loop invariant i == 1 ==> f == 1;
      loop invariant i == 2 ==> f == 1;
      loop invariant i == 3 ==> f == 2;
      loop invariant i == 4 ==> f == 6;
      loop invariant i == 5 ==> f == 24;
      loop invariant i == 6 ==> f == 120;
      loop assigns i, f;
      loop variant n - i + 1;
    */
    for (i = 1; i <= n; i++)
        f = f * i;
    
    return f;
}



//5 messages total (with Claude Sonnet 4.5)