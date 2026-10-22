module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numEquiv_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.setCongr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

variable {α β : Type*}

/-- `P N ≅ P N × P N` — `N ≅ N ⊕ N` together with `P(A ⊕ B) ≅ P A × P B` (`Set.sumEquiv`). -/
def PN_orderIso_prod : Set ℕ ≃o Set ℕ × Set ℕ :=
  (setCongr Equiv.natSumNatEquivNat.symm).trans Set.sumEquiv

end DomainTheory.NeighbourhoodSystems.Exercise513
