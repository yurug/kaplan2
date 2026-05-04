# Tiny Makefile for the example program.  Two build modes:
#
#   make            — build against the in-tree library (../include + ../)
#   make installed  — build against the installed library (uses pkg-config)
#
# Run with `./hello` after either.

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11

.PHONY: all installed clean

all: hello

# In-tree build: assumes you've run `make` in c/ already so libktdeque.a
# sits next to this directory in c/.
hello: hello.c ../libktdeque.a ../include/ktdeque.h
	$(CC) $(CFLAGS) -I../include -L.. -o $@ hello.c -lktdeque

# Build against the installed library via pkg-config.
installed: hello.c
	$(CC) $(CFLAGS) -o hello hello.c $(shell pkg-config --cflags --libs ktdeque)

clean:
	rm -f hello
