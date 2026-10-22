module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- Its uncurried form, the actual `N × N → N` of the exercise. -/
def numP (p : ℕ × ℕ) : ℕ := num p.1 p.2

end DomainTheory.NeighbourhoodSystems.Exercise513
