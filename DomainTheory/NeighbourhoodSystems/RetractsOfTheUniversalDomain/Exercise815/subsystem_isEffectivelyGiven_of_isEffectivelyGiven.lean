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
