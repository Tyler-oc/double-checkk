#include <stdio.h>

int find_max(int nums[], int size)
{
    int max = nums[0];
    for (int i = 1; i < size; i++)
    {
        if (nums[i] > max)
        {
            max = nums[i];
        }
    }
    return max;
}

int main()
{
    int numbers[] = {3, 5, 7, 2, 8};
    int max_value = find_max(numbers, 5);
    printf("The maximum value is: %d\n", max_value);
    return 0;
}