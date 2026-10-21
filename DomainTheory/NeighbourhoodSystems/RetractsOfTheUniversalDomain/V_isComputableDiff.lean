/-ai
A computable set difference for the presentation of V takes the canonical difference index, together with its primitive recursiveness, its correctness whenever a representing index exists, and the recursive decidability of that existence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_diff_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_Vdiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff_spec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `\`**, the missing prerequisite for Exercise 8.12(f). -/
def V_isComputableDiff : IsComputableDiff VComputablePresentation where
  diffIdx := Vdiff
  diffIdx_primrec := primrec_Vdiff
  diffIdx_spec := Vdiff_spec
  diff_computable := V_diff_computable

end DomainTheory.NeighbourhoodSystems
