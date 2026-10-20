module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}









/-- **Exercise 8.17, Part 1 (`→`).** `iArrow/jArrow` already are the pair `𝒰→𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem funSpaceUU_trianglelefteq_U : funSpace U U ⊴ U :=
  trianglelefteq_of_projectionPair iArrow jArrow jArrow_comp_iArrow iArrow_comp_jArrow_le

end DomainTheory.NeighbourhoodSystems
