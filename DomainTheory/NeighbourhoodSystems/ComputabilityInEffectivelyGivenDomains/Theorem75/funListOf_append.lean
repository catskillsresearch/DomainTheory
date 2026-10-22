module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


theorem funListOf_append (la lb : List ℕ) :
    funListOf P₀ P₁ (la ++ lb) = funListOf P₀ P₁ la ++ funListOf P₀ P₁ lb := by
  simp [funListOf, List.map_append]

end DomainTheory.NeighbourhoodSystems
