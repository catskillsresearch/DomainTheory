/-ai
This file gathers and re-exports the classification of subsets of Pω: the basic constructions, Theorems 6.1 through 6.5, the identity of the indexed pairing at the top element and of the odd-even packing at zero, continuity and the value of the closed-and-Gδ packing, the failure of zero to lie in the successor of the top element, closure of the Bδ class under intersection and union, and the typical sets for the Scott-open, Scott-closed, Scott Gδ, closed-and-open, closed-and-Gδ, Bδ, Σ¹₁, and Π¹₁ classes, together with their membership and universality statements.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Classification.Basic
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_1
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_2
public import DomainTheory.DataTypesAsLattices.Classification.pairIndexed_eq_top
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_3
public import DomainTheory.DataTypesAsLattices.Classification.oddEvenPack_eq_zero
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_4
public import DomainTheory.DataTypesAsLattices.Classification.fcapGdeltaPack_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Classification.zero_not_mem_succSet_top
public import DomainTheory.DataTypesAsLattices.Classification.fcapGdeltaPack_eq
public import DomainTheory.DataTypesAsLattices.Classification.theorem_6_5
public import DomainTheory.DataTypesAsLattices.Classification.isBdelta_inter
public import DomainTheory.DataTypesAsLattices.Classification.isBdelta_union
public import DomainTheory.DataTypesAsLattices.Classification.typicalG_isScottOpen
public import DomainTheory.DataTypesAsLattices.Classification.typicalG_mem_ScottG
public import DomainTheory.DataTypesAsLattices.Classification.typicalG_universal
public import DomainTheory.DataTypesAsLattices.Classification.typicalF_mem_ScottF
public import DomainTheory.DataTypesAsLattices.Classification.typicalF_universal
public import DomainTheory.DataTypesAsLattices.Classification.typicalGdelta_eq
public import DomainTheory.DataTypesAsLattices.Classification.typicalGdelta_isScottGdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalGdelta_universal
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapG_isFcapG
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapG_universal
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapGdelta_isFcapGdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalFcapGdelta_universal
public import DomainTheory.DataTypesAsLattices.Classification.typicalBdelta_isBdelta
public import DomainTheory.DataTypesAsLattices.Classification.typicalSigma11_isSigma11
public import DomainTheory.DataTypesAsLattices.Classification.typicalSigma11_universal
public import DomainTheory.DataTypesAsLattices.Classification.typicalPi11_isPi11
public import DomainTheory.DataTypesAsLattices.Classification.typicalPi11_universal

@[expose] public section
