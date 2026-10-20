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

/-- **Proposition 6.12, second law: `i ∘ j ⊆ I_E`.** A round trip `Y ⊆ X ⊆ Y'` through a common
`D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E`. The reverse inclusion fails (not every
consistent `E`-pair factors through `D`), so this is an inclusion of relations, not an equality. -/
theorem inj_comp_proj_le (h : D ◁ E) : h.inj.comp h.proj ≤ idMap E := by
  intro Y Y' hr
  obtain ⟨X, ⟨hEY, _, hYX⟩, _, hEY', hXY'⟩ := hr
  exact ⟨hEY, hEY', hYX.trans hXY'⟩

end Subsystem

end DomainTheory.NeighbourhoodSystems
