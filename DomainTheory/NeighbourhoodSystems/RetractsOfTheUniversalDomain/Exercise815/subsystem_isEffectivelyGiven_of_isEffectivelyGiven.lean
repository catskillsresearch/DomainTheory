/-ai
If a neighbourhood system is effectively given, then some effectively given neighbourhood system on lists of natural numbers has elements order-isomorphic to its subsystems.

A computable presentation of the system determines the system of its finitely generated subsystems. That system is effectively given by the presentation built from the same data, and the order isomorphism of its elements with the subsystems is the isomorphism already constructed for that presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}


/-- **Exercise 8.15, first half.** If `D` is effectively given, there is an effectively given
neighbourhood system (`SubD P`, on tokens `List ℕ`) whose elements are order-isomorphic to
`{D' ∣ D' ◁ D}` — a *direct*, choice-free construction (Subgoals 1–4), unlike the classical route
through `Exercise222.reprIso` (`Proposition611.subsystemReprIso`). -/
theorem subsystem_isEffectivelyGiven_of_isEffectivelyGiven (hD : D.IsEffectivelyGiven) :
    ∃ V : NeighborhoodSystem (List ℕ), V.IsEffectivelyGiven ∧
      Nonempty (V.Element ≃o {D' : NeighborhoodSystem α // D' ◁ D}) := by
  obtain ⟨P⟩ := hD
  exact ⟨SubD P, ⟨SubDPresentation P⟩, ⟨subsystemIso P⟩⟩

end DomainTheory.NeighbourhoodSystems
