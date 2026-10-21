/-ai
A heterogeneous projection pair from one neighbourhood system to another consists of an approximable injection, an approximable projection, the equality of the projection after the injection with the identity of the source, and the inequality of the injection after the projection with the identity of the target.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4

@[expose] public section

universe u v w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **A heterogeneous projection pair** — the raw data `Lemma615.trianglelefteq_of_projectionPair`
consumes, bundled for easy composition. -/
structure ProjPair (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E

end DomainTheory.NeighbourhoodSystems
