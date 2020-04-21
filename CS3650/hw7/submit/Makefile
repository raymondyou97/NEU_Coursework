# First target is default target, if you just type:  make
# Makefile copied from hw4, just changed file target
FILE=RaymondYouHW7Cache.c

default: run

run: CacheSim
	./CacheSim

gdb: CacheSim
	gdb --args CacheSim

#Had to add -std=c99 to compile in mobaxterm. Remove it if it doesn't compile
CacheSim: ${FILE}
	gcc -g -O0 -o CacheSim ${FILE} -std=c99

emacs: ${FILE}
	emacs ${FILE}
vi: ${FILE}
	vi ${FILE}

clean:
	rm -f CacheSim a.out *~

# 'make' views $v as a make variable and expands $v into the value of v.
# By typing $$, make will reduce it to a single '$' and pass it to the shell.
# The shell will view $dir as a shell variable and expand it.
dist:
	dir=`basename $$PWD`; cd ..; tar cvf $$dir.tar ./$$dir; gzip $$dir.tar
	dir=`basename $$PWD`; ls -l ../$$dir.tar.gz
