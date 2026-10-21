/-ai
The standard naturals, with zero and successor, form a Peano model. Zero differs from every successor, successor is injective, and a subset containing zero and closed under successor contains every natural by induction on that natural.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- *(For set theorists.)* The standard natural numbers `⟨ℕ, 0, ⁺⟩` form a model of Peano's Axioms;
their existence is the **axiom of infinity**. (This witnesses that an `N*` satisfying (i)/(ii) — in
fact all three — exists in the first place.) -/
def natPeano : PeanoModel ℕ where
  zero := 0
  succ := Nat.succ
  zero_ne_succ n := (Nat.succ_ne_zero n).symm
  succ_injective := Nat.succ_injective
  induction s h0 hstep := by
    intro n
    induction n with
    | zero => exact h0
    | succ k ih => exact hstep k ih

end DomainTheory.NeighbourhoodSystems.Exercise422
