/-ai
This module gathers and re-exports the basic development of Pω together with the results on the coded finite sets, their codes, and the pairing function: emptiness of the set coded by 0, the bound k < 2^k, the strict membership bound, finiteness, powers of two as singletons, unions of codes, existence of a finite piece containing a given element, bitwise disjunction, list and finite-set codes, existence of a code for every finite set, monotonicity and strict increase of the triangular numbers, the triangular bounds on a pair, injectivity of pairing, the inequalities for the two components, and the pairing and unpairing identities.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e_zero
public import DomainTheory.DataTypesAsLattices.Pomega.lt_two_powu27
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e_lt
public import DomainTheory.DataTypesAsLattices.Pomega.e_finite
public import DomainTheory.DataTypesAsLattices.Pomega.e_pow2
public import DomainTheory.DataTypesAsLattices.Pomega.singleton_eq_e
public import DomainTheory.DataTypesAsLattices.Pomega.union_e_eq
public import DomainTheory.DataTypesAsLattices.Pomega.exists_e_mem
public import DomainTheory.DataTypesAsLattices.Pomega.e_or
public import DomainTheory.DataTypesAsLattices.Pomega.e_or_of_subset
public import DomainTheory.DataTypesAsLattices.Pomega.e_codeList
public import DomainTheory.DataTypesAsLattices.Pomega.e_codeFinset
public import DomainTheory.DataTypesAsLattices.Pomega.exists_code
public import DomainTheory.DataTypesAsLattices.Pomega.exists_code_of_finite
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_le_of_le
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_lt_of_lt
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_le_pair
public import DomainTheory.DataTypesAsLattices.Pomega.pair_inj
public import DomainTheory.DataTypesAsLattices.Pomega.pair_le_left
public import DomainTheory.DataTypesAsLattices.Pomega.pair_le_right
public import DomainTheory.DataTypesAsLattices.Pomega.pair_unpair
public import DomainTheory.DataTypesAsLattices.Pomega.unpair_pair
public import DomainTheory.DataTypesAsLattices.Pomega.pair_lt_left
public import DomainTheory.DataTypesAsLattices.Pomega.pair_lt_right

@[expose] public section
