/-ai
This file gathers and re-exports the fixed-point development: the basic imports, the diagonal, composition, unary, binary, and ternary forms of the substitution theorem, monotonicity of chains, the finite-index lemma, the chain lemma, monotonicity of iteration from the bottom element, and the fixed-point theorem.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_diag
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_comp
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_tuple
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_nary
public import DomainTheory.DataTypesAsLattices.FixedPoint.chain_mono
public import DomainTheory.DataTypesAsLattices.FixedPoint.exists_index_of_finset
public import DomainTheory.DataTypesAsLattices.FixedPoint.chain_lemma
public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot_mono
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4

@[expose] public section
