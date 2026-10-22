module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.le_iff_isOpen_imp
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace NeighborhoodSystem

/-- A continuous function between domains is monotone for the approximation order `⊑`: this is
because `⊑` is recoverable from the topology (`le_iff_isOpen_imp`) and continuous preimages of opens
are open and upward closed (`isOpen_isUpperSet`). -/
theorem continuous_monotone {c : V₀.Element → V₁.Element} (hc : Continuous c) : Monotone c := by
  intro x y hxy
  rw [V₁.le_iff_isOpen_imp]
  intro U hU hxU
  exact V₀.isOpen_isUpperSet (hU.preimage hc) hxU hxy

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
