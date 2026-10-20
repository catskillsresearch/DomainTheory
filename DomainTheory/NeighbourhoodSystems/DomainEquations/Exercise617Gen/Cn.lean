module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Strn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.mem_coneN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.coneN_nil
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.memCn
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.nestedOrDisjointN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

variable {A : Type} [DecidableEq A]

/-- **The generic domain `Cₐ`** of finite-or-infinite `A`-sequences. -/
abbrev Cn (A : Type) [DecidableEq A] : NeighborhoodSystem (Strn A) :=
  NeighborhoodSystem.ofNestedOrDisjoint memCn Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], coneN_nil.symm⟩) nestedOrDisjointN
    (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
