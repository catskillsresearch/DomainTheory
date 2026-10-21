/-ai
The uncurried pairing function sends a pair of natural numbers to the pairing function of its two components.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- Its uncurried form, the actual `N × N → N` of the exercise. -/
def numP (p : ℕ × ℕ) : ℕ := num p.1 p.2

end DomainTheory.NeighbourhoodSystems.Exercise513
