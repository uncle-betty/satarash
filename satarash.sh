#!/bin/bash

set -u

CADICAL=${HOME}/.local/bin/cadical
DRAT_TRIM=${HOME}/.local/bin/drat-trim
CHECKER=${HOME}/.local/bin/Checker

CNF=/tmp/${BASHPID}.cnf
DRAT=/tmp/${BASHPID}.drat
LRAT=/tmp/${BASHPID}.lrat

rm -f ${CNF} ${DRAT} ${LRAT}

check_result() {
    if [ ${?} -ne 0 ]; then
        rm -f ${CNF} ${DRAT} ${LRAT}
        echo ${1}
        exit 1
    fi
}

cat >${CNF}

${CADICAL} ${CNF} ${DRAT} 2>&1 | grep "s UNSATISFIABLE" >/dev/null
check_result cadical

${DRAT_TRIM} ${CNF} ${DRAT} -L ${LRAT} 2>&1 | grep "s VERIFIED" >/dev/null
check_result drat-trim

${CHECKER} ${CNF} ${LRAT} 2>&1 | grep ok >/dev/null
check_result checker

rm -f ${CNF} ${DRAT} ${LRAT}
echo ok
exit 0
