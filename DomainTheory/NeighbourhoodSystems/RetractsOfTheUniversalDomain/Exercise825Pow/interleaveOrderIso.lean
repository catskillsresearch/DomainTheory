module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import Mathlib.Logic.Equiv.Nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.arrowReindexOrderIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow.sumArrowOrderIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- **Interleaving.** Two `ℕ`-indexed sequences of `E` can be merged, order-isomorphically, into a
single `ℕ`-indexed sequence, via the pairing bijection `ℕ ⊕ ℕ ≃ ℕ`. -/
def interleaveOrderIso (E : Type*) [Preorder E] : (ℕ → E) × (ℕ → E) ≃o (ℕ → E) :=
  (sumArrowOrderIso ℕ ℕ E).symm.trans (arrowReindexOrderIso Equiv.natSumNatEquivNat E)

end DomainTheory.NeighbourhoodSystems
