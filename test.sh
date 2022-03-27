#!/bin/bash

TRIM=../drat-trim
NAMES="
    example-4-vars
    example-5-vars
    example-Schur
    R_4_4_18
    uuf-100-1
    uuf-100-2
    uuf-100-3
    uuf-100-4
    uuf-100-5
    uuf-30-1
    uuf-50-2
    uuf-50-3
"

RUN=./Checker

for NAME in ${NAMES}; do
    echo ${NAME}
    ${RUN} ${TRIM}/examples/${NAME}.cnf ${TRIM}/examples/${NAME}.lrat
done

echo big_add
${RUN} test/big_add.cnf test/big_add.lrat

echo mul_com
${RUN} test/mul_com.cnf test/mul_com.lrat
