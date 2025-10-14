/*@
  requires length > 0;
  requires \valid_read(arr + (0..length-1));
  assigns \nothing;
  ensures
    \exists integer k; 0 <= k < length && \result == arr[k];
  ensures
    \forall integer i; 0 <= i < length ==> \result >= arr[i];
*/
int find_max(int arr[], int length) {
    int max = arr[0];
    /*@
      loop invariant 0 <= i <= length;
      loop invariant \forall integer j; 0 <= j < i ==> max >= arr[j];
      loop invariant \exists integer k; 0 <= k < length && max == arr[k];
      loop assigns i, max;
      loop variant length - i;
    */
    for(int i = 1; i < length; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    return max;
}

/*@
  assigns \nothing;
*/
int main() {
    int arr[] = {1, 2, 4, 2, 8, 3};
    int length = 6;
    int result = find_max(arr, length);
    return 0;
}