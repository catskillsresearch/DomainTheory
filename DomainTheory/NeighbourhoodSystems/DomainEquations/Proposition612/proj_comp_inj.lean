module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.ProjectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12, first law: `j ∘ i = I_D`.** Each side relates `X` and `Z` exactly when
`X, Z ∈ D` and `X ⊆ Z`: a round trip `X ⊆ Y ⊆ Z` through an `E`-neighbourhood `Y` collapses to
`X ⊆ Z` (forward), and `X ⊆ Z` factors through `Y = Z` (backward). Proved relationally, so
**choice-free**. -/
theorem proj_comp_inj (h : D ◁ E) : h.proj.comp h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, _, hZ, hYZ⟩
    exact ⟨hX, hZ, hXY.trans hYZ⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨Z, ⟨hX, h.sub hZ, hXZ⟩, h.sub hZ, hZ, subset_rfl⟩

end Subsystem

end DomainTheory.NeighbourhoodSystems
