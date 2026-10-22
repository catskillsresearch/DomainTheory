module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- The code of the one-entry function-space neighbourhood `[⟨X_{e.1}, X_{e'.1}⟩, X_{e'.2}]` of
`(𝒟₀×𝒟₁→𝒟₂)` (a `Xenum`-singleton over the product presentation). -/
def curryStepCode (a e' : ℕ) : ℕ :=
  Nat.pair (Nat.pair (Nat.pair a e'.unpair.1) e'.unpair.2) 0 + 1

end DomainTheory.NeighbourhoodSystems
