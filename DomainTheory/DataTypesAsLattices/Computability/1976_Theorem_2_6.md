# Theorem 2.6

@import "1976_Theorem_2_6.english" {code_block=false}

## Motivation

The three conditions meet as follows. Passing from a computable $f$ to its iterated graph replaces $m \in f(e_{n_0})(e_{n_1}) \cdots (e_{n_{k-1}})$ by membership of the iterated pair $(n_0, (n_1, (\cdots, (n_{k-1}, m) \cdots)))$ in that graph, so the function is computable exactly when the graph is r.e. The hint above shows that an r.e. graph is LAMBDA-definable. In the other direction each of the six combinators of Theorem 2.4 is r.e., and application preserves r.e. sets: $m \in u(x)$ is an existential quantification over a finite $e_n \subseteq x$ together with a bounded universal quantification, and membership in $u$ and in $x$ occurs positively.

**[DataTypesAsLattices/Computability/lt_two_pow_of_high_bits.lean](lt_two_pow_of_high_bits.lean)**

@import "lt_two_pow_of_high_bits.lean"
**[DataTypesAsLattices/Computability/REPredu2etrue.lean](REPredu2etrue.lean)**

@import "REPredu2etrue.lean"
**[DataTypesAsLattices/Computability/enumFun.lean](enumFun.lean)**

@import "enumFun.lean"
**[DataTypesAsLattices/Computability/eSubset_funOf_e_iff.lean](eSubset_funOf_e_iff.lean)**

@import "eSubset_funOf_e_iff.lean"
**[DataTypesAsLattices/Computability/pairTerm.lean](pairTerm.lean)**

@import "pairTerm.lean"
**[DataTypesAsLattices/Computability/eSubset_e_iff.lean](eSubset_e_iff.lean)**

@import "eSubset_e_iff.lean"
**[DataTypesAsLattices/Computability/unpairFstTerm.lean](unpairFstTerm.lean)**

@import "unpairFstTerm.lean"
**[DataTypesAsLattices/Computability/REPredu2eor.lean](REPredu2eor.lean)**

@import "REPredu2eor.lean"
**[DataTypesAsLattices/Computability/eSubset_iff_stage.lean](eSubset_iff_stage.lean)**

@import "eSubset_iff_stage.lean"
**[DataTypesAsLattices/Computability/REPredu2eempty.lean](REPredu2eempty.lean)**

@import "REPredu2eempty.lean"
**[DataTypesAsLattices/Computability/mem_graph_const_iff.lean](mem_graph_const_iff.lean)**

@import "mem_graph_const_iff.lean"
**[DataTypesAsLattices/Computability/bits_subset_lt_two_pow.lean](bits_subset_lt_two_pow.lean)**

@import "bits_subset_lt_two_pow.lean"
**[DataTypesAsLattices/Computability/precTerm.lean](precTerm.lean)**

@import "precTerm.lean"
**[DataTypesAsLattices/Computability/IsRE.lean](IsRE.lean)**

@import "IsRE.lean"
**[DataTypesAsLattices/Enumeration/applyNat.lean](../Enumeration/applyNat.lean)**

@import "../Enumeration/applyNat.lean"
**[DataTypesAsLattices/Enumeration/num.lean](../Enumeration/num.lean)**

@import "../Enumeration/num.lean"
