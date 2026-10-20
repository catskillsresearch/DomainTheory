module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `V` — witnessed directly by `Vunion`. -/
theorem V_union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion_spec n m⟩

end DomainTheory.NeighbourhoodSystems
