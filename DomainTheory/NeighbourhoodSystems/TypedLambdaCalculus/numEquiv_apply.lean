module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

@[simp] theorem numEquiv_apply (p : ℕ × ℕ) : numEquiv p = num p.1 p.2 := rfl

end DomainTheory.NeighbourhoodSystems.Exercise513
