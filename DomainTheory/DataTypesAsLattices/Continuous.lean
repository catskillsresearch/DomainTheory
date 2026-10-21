/-ai
This file gathers and re-exports the development of Scott continuity on Pω: the basic notions, Scott-open sets and the fact that they are upper sets, membership in a Scott union, monotonicity of Scott-continuous maps, finite covers by basic elements, Theorem 1.1, determination of a Scott-continuous map by its values, openness of the sets of elements containing a fixed finite piece, the expression of a basic neighborhood as an intersection, openness and binary intersection of basic neighborhoods together with the zero neighborhood, the equality of those membership opens with basic neighborhoods, the existence of a basic neighborhood inside a generated open, the equivalence of Scott-open and topologically open sets, and the equivalence of Scott continuity with topological continuity.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_basic
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_monotone
public import DomainTheory.DataTypesAsLattices.Continuous.exists_e_cover_finite
public import DomainTheory.DataTypesAsLattices.Continuous.theorem_1_1
public import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_determined
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_memOpen
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd_eq_iInter
public import DomainTheory.DataTypesAsLattices.Continuous.isOpen_basicNhhd
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd_inter
public import DomainTheory.DataTypesAsLattices.Continuous.basicNhhd_zero
public import DomainTheory.DataTypesAsLattices.Continuous.memOpen_eq_basicNhhd
public import DomainTheory.DataTypesAsLattices.Continuous.exists_basicNhhd_subset_of_generateOpen
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_iff_isOpen
public import DomainTheory.DataTypesAsLattices.Continuous.isScottContinuous_iff_continuous

@[expose] public section
