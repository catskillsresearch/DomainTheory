module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.ProjectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_comp_proj_le

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **Proposition 6.12 (Scott 1981, PRG-19).** Every subdomain relation `D ◁ E` gives rise to a
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. -/
def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end Subsystem

end DomainTheory.NeighbourhoodSystems
