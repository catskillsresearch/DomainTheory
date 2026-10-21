/-ai
A function from naturals to sets of naturals that sends zero to every natural and sends m + 1 to the successor image of its value at m is equal to the up-set function.

Compare values by induction on the argument. At zero, rewrite by the given base and the law that the up-set of zero is every natural. At a successor, rewrite by the given step, the inductive hypothesis, and the law that the up-set of a successor is the successor image of the previous up-set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414







/-- **Exercise 4.21 / 4.13(3) (Scott 1981, PRG-19).** `[·] = upSet` is the *unique* function with
`[0] = ℕ` and `[m⁺] = [m]⁺`. -/
theorem upSet_unique (s : ℕ → Set ℕ) (h0 : s 0 = Set.univ)
    (hsucc : ∀ m, s (m + 1) = succImage (s m)) : s = upSet := by
  funext m
  induction m with
  | zero => rw [h0, upSet_zero]
  | succ k ih => rw [hsucc k, ih, upSet_succ]

end DomainTheory.NeighbourhoodSystems.Exercise421
