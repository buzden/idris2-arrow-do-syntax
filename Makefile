export IDRIS2 ?= idris2

RUNTESTS := build/exec/runtests

MKDIR := mkdir -p
LN := ln

.PHONY: all arrows-do-syntax clean

all: arrows-do-syntax

arrows-do-syntax:
	${IDRIS2} --build arrows-do-syntax.ipkg

clean:
	${IDRIS2} --clean arrows-do-syntax.ipkg
	${RM} -r build
	@
	${MAKE} -C tests -f tests.mk clean

.PHONY: test test-arrows-do-syntax

test: test-arrows-do-syntax

test-arrows-do-syntax: arrows-do-syntax
	${MAKE} -C tests -f tests.mk only="${only}"
