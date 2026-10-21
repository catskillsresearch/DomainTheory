/-ai
The family C is nonempty.

It contains the graph of the constant approximable map whose value is the bottom neighbourhood of the second system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem C_nonempty : (C V₀ V₁).Nonempty :=
  ⟨graph (constMap V₀ V₁.bot), constMap V₀ V₁.bot, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
