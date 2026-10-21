/-ai
The step pair of a code e is the pair whose first component is the domain neighbourhood indexed by the first half of the unpairing of e and whose second component is the codomain neighbourhood indexed by the second half.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- The step pair coded by an entry `e`: `(X_{e.unpair.1}, Y_{e.unpair.2})`. -/
def funPair (e : ℕ) : Set α × Set β := (P₀.X e.unpair.1, P₁.X e.unpair.2)

end DomainTheory.NeighbourhoodSystems
