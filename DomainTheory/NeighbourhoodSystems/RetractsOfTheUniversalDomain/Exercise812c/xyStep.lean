module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

def xyStep {α γ : Type*} (split : Set α → Set γ → Set α → Set γ × Set γ)
    (A : Set α) (B : Set γ) (Xn : Set α) (b : Bool) : Set α × Set γ :=
  (if b then A ∩ Xn else A \ Xn, if b then (split A B Xn).1 else (split A B Xn).2)

end DomainTheory.NeighbourhoodSystems
