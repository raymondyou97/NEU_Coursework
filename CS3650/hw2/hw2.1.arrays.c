#include <stdio.h>
#define IN   1  /* inside a word */
#define OUT  0  /* outside a word */

/* count lines, words, and characters in input */
/* to run, try:    gcc THIS_FILE.c ; cat ANY_FILE | ./a.out */

main()
{
    int nl, nw, nc, state;
	char x1[100] = "The quick brown fox jumped over the lazy dog.\n";
	int i = 0;
    state = OUT;
    nl = nw = nc = 0;
    while (x1[i] != '\0') {
        ++nc;
        if (x1[i] == '\n')
            ++nl;
        if (x1[i] == ' ' || x1[i] == '\n' || x1[i] == '\t')
            state = OUT;
        else if (state == OUT) {
            state = IN;
            ++nw;
        }
		i++;
    }
    printf("%d %d %d\n", nl, nw, nc);
    return 0;
}
