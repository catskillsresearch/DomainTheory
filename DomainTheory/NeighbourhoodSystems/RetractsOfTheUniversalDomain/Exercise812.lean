/-ai
This file gathers and re-exports the basic layer of Exercise 8.12, nonemptiness of a residue class whose remainder lies below the modulus, emptiness of a residue class whose remainder is at least the modulus, the nonemptiness criterion for a level set, the identification of a residue class with a one-bit level set, the decomposition of a level set as a finite union of residue classes, intersection and union of level sets at one common level, the splitting of every neighbourhood of V into two proper pieces, closure of V under binary and finite unions, and the characterization of the neighbourhoods of V as the nonempty finite unions of residue classes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.affine_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.affine_eq_empty_of_ge
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_nonempty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.affine_eq_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_eq_biUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_inter_same_level
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.levelSet_union_same_level
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_union_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_iUnion_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_mem_iff_finiteUnion

@[expose] public section
