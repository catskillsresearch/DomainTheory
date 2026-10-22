module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numEquiv
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numEquiv_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.setCongr

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

variable {α β : Type*}

/-- `P N ≅ P(N × N)` — induced by the pairing bijection `numEquiv`. -/
def PN_orderIso_PNN : Set ℕ ≃o Set (ℕ × ℕ) := setCongr numEquiv.symm

end DomainTheory.NeighbourhoodSystems.Exercise513
