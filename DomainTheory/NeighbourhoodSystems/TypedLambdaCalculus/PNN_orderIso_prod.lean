/-ai
The power set of pairs of natural numbers is order-isomorphic to the product of two power sets of natural numbers, as the composite of the inverse of the pairing isomorphism with the isomorphism induced by the decomposition of the naturals as a disjoint sum.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
import all Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numEquiv_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.PN_orderIso_PNN
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.PN_orderIso_prod

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

variable {α β : Type*}

/-- `P(N × N) ≅ P N × P N` — by composing the two isomorphisms above. -/
def PNN_orderIso_prod : Set (ℕ × ℕ) ≃o Set ℕ × Set ℕ :=
  PN_orderIso_PNN.symm.trans PN_orderIso_prod

end DomainTheory.NeighbourhoodSystems.Exercise513
