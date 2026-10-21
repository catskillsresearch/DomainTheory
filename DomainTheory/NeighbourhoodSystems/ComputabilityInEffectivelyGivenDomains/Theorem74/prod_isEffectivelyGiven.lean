/-ai
The product of two effectively given neighbourhood systems is effectively given.

Unpack the two computable presentations and package them as the product presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}





/-- **Theorem 7.4 (Scott 1981, PRG-19).** The product of effectively given domains is effectively
given. -/
theorem prod_isEffectivelyGiven (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (prod V₀ V₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := h₀; obtain ⟨P₁⟩ := h₁
  exact ⟨prodPresentation P₀ P₁⟩

end DomainTheory.NeighbourhoodSystems
