#include <stdio.h>

//using array-style pointers here too because hw said to
/* count digits, white space, others */
/* to run, try:    gcc THIS_FILE.c ; cat ANY_FILE | ./a.out */

main()
{
    int i, nwhite, nother;
    int ndigit[10];
    nwhite = nother = 0;
	char x1[100] = "The 25 quick brown foxes jumped over the 27 lazy dogs 17 times.";
	char *x1ptr = x1;
    for (i = 0; i < 10; ++i)
        ndigit[i] = 0;
    while (*(x1ptr + i) != '\0') {
        if (*(x1ptr + i) >= '0' && *(x1ptr + i) <= '9')
            ++ndigit[x1[i]-'0'];
        else if (*(x1ptr + i) == ' ' || *(x1ptr + i) == '\n' || *(x1ptr + i) == '\t')
            ++nwhite;
        else
            ++nother;
		i++;
    }
    printf("digits =");
    for (i = 0; i < 10; ++i)
        printf(" %d", ndigit[i]);
    printf(", white space = %d, other = %d\n",
        nwhite, nother);
    return 0;
}
