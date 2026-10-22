module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The one-entry function-space code: `Xenum (codePair a b) = [X_a, X_b]`. -/
def codePair (a b : ℕ) : ℕ := Nat.pair (Nat.pair a b) 0 + 1

end DomainTheory.NeighbourhoodSystems
