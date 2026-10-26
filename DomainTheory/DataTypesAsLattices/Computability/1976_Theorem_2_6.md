# Theorem 2.6

@import "1976_Theorem_2_6.english" {code_block=false}

## Motivation

The three conditions meet as follows. Passing from a computable $f$ to its iterated graph replaces $m \in f(e_{n_0})(e_{n_1}) \cdots (e_{n_{k-1}})$ by membership of the iterated pair $(n_0, (n_1, (\cdots, (n_{k-1}, m) \cdots)))$ in that graph, so the function is computable exactly when the graph is r.e. The hint above shows that an r.e. graph is LAMBDA-definable. In the other direction each of the six combinators of Theorem 2.4 is r.e., and application preserves r.e. sets: $m \in u(x)$ is an existential quantification over a finite $e_n \subseteq x$ together with a bounded universal quantification, and membership in $u$ and in $x$ occurs positively.

**[DataTypesAsLattices/Computability/theorem_2_6.lean](theorem_2_6.lean)**

@import "theorem_2_6.lean"

**[DataTypesAsLattices/Computability/theorem_2_6.combinatory_zero.lean](theorem_2_6.combinatory_zero.lean)**

@import "theorem_2_6.combinatory_zero.lean"

**[DataTypesAsLattices/Computability/theorem_2_6.fin.lean](theorem_2_6.fin.lean)**

@import "theorem_2_6.fin.lean"

**[DataTypesAsLattices/Computability/theorem_2_6.lambda_continuous.lean](theorem_2_6.lambda_continuous.lean)**

@import "theorem_2_6.lambda_continuous.lean"

**[DataTypesAsLattices/Computability/theorem_2_6.ofNat_isRE.lean](theorem_2_6.ofNat_isRE.lean)**

@import "theorem_2_6.ofNat_isRE.lean"

**[DataTypesAsLattices/Computability.lean](../Computability.lean)**

@import "../Computability.lean"

