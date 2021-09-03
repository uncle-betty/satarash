**Sataraš (satarash)**

Today's SAT solvers are able to produce a proof of an unsatisfiability result
they arrived at for a given Boolean formula. In order to keep honest SAT
solvers honest, we should verify these proofs. Ideally, this would be done with
a certified verifier.

Sataraš is my attempt at naively implementing such a certified verifier while
learning Agda. More efficient certified verifiers exist, implemented in Coq or
ACL2, for example.

SAT solvers produce what's known as *DRAT proofs*. They can be converted into
equivalent *LRAT proofs*, which are easier to verify.

Sataraš follows the verification algorithm for LRAT proofs put forward in the
paper that first introduced them: *Efficient Certified RAT Verification*. It's
available here: https://www.cs.utexas.edu/users/marijn/publications/lrat.pdf

For a C++ prototype of the verifier, say `make checker` in the top-level
directory of this repository. For the Agda version, say `make Checker`. As of
this writing, I'm using the latest version of Agda and the standard library
available from the Agda GitHub repo.

Let's take a look at the `mul_com.v` example in the `test` subdirectory to see
how things fit together. It's the Verilog description of a combinational
circuit (= a Boolean formula) that outputs (= evaluates to) `true`, if the
multiplication of two 10-bit values isn't commutative. Proving the formula
unsatisfiable proves that 10-bit multiplication is commutative.

  * SAT solvers operate on Boolean formulas given in CNF. We thus need to turn
    our Verilog code into a formula in CNF. For that, we use the open-source
    Verilog synthesis suite *Yosys*, which is available here:
    https://github.com/YosysHQ/yosys

    The `synth.sh` script in the `test` subdirectory simplifies running Yosys
    in order to produce `mul_com.cnf`, which contains the CNF corresponding to
    the Verilog code.

  * Next, we need a SAT solver to prove the formula in `mul_com.cnf`
    unsatisfiable. I use *Cadical*, which can be found here:
    https://github.com/arminbiere/cadical

    In order to produce a DRAT proof of `mul_com.cnf`'s unsatisfiability, run
    `cadical mul_com.cnf mul_com.drat`. This writes the DRAT proof to
    `mul_com.drat`.

  * Next, we need to turn the DRAT proof into an LRAT proof. That's what
    *drat-trim* is for, which can be found here:
    https://github.com/marijnheule/drat-trim

    The conversion is done with
    `drat-trim mul_com.cnf mul_com.drat -L mul_com.lrat`.
    This writes the LRAT proof to `mul_com.lrat`. In the repo, this file is
    compressed so that it doesn't exceed GitHub's file size limit.

  * Finally, we can verify that `mul_com.lrat` is, in fact, a proof of
    `mul_com.cnf`'s unsatisfiability. From within the `test` subdirectory, run
    `../Checker mul_com.cnf mul_com.lrat` and wait for an `ok` result. This may
    take a while. As said above, the implementation and the formula
    representation of the checker is pretty naive.

The format used to express the CNF is called *DIMACS*. Note that my DIMACS
parser is a little finicky. It doesn't accept comment lines, empty lines, or
more than one space between tokens.
