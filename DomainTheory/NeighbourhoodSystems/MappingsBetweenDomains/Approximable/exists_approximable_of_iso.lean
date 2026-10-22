/-ai
Every order isomorphism between the elements of two neighbourhood systems is the elementwise action of some approximable map.

The approximable map induced by the isomorphism has that elementwise action.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_ofIso

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.7 (statement) (Scott 1981, PRG-19).** "Every isomorphism between domains results from
an approximable mapping." For any domain isomorphism `e`, there is an approximable mapping whose
elementwise action is exactly `e`. -/
theorem exists_approximable_of_iso (e : V₀.Element ≃o V₁.Element) :
    ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x :=
  ⟨ofIso e, toElementMap_ofIso e⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
