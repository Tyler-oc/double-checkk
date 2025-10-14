#include <stdio.h>

int find_max(int arr[])
{
}

int is_greater(int a, int b)
{
    return a > b;
}

int main()
{
    int x = 10;
    int y = 20;
    printf("x: %d, y: %d\n", x, y);
    if (is_greater(y, x))
    {
        printf("y is greater than x\n");
    }
    else
    {
        printf("x is greater than or equal to y\n");
    }
    return 0;
}