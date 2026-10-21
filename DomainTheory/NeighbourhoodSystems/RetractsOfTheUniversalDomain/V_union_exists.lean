/-ai
The union of two enumerated neighbourhoods of V equals the enumerated neighbourhood of their union index.

The union index is a witness, by the specification of that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Xₙ ∪ Xₘ` is always presentable as some `X_k`**, for `V` — witnessed directly by `Vunion`. -/
theorem V_union_exists (n m : ℕ) : ∃ k, VX k = VX n ∪ VX m := ⟨Vunion n m, Vunion_spec n m⟩

end DomainTheory.NeighbourhoodSystems
