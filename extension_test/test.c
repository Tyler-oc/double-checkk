#include <stdio.h>
#include <stdlib.h>

// Comparison function for integers
int compare_ints(const void *a, const void *b)
{
    int arg1 = *(const int *)a;
    int arg2 = *(const int *)b;

    if (arg1 < arg2)
        return -1;
    if (arg1 > arg2)
        return 1;
    return 0;

    // A common shortcut is: return (arg1 > arg2) - (arg1 < arg2);
}

int main()
{
    int ints[] = {-2, 99, 0, -743, 2, 4};
    int size = sizeof(ints) / sizeof(ints[0]);

    // Sort the array using qsort
    qsort(ints, size, sizeof(int), compare_ints);

    printf("Sorted array: ");
    for (int i = 0; i < size; i++)
    {
        printf("%d ", ints[i]);
    }
    printf("\n");

    return 0;
}
