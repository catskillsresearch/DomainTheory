/-ai
A defaulted reading of an append, at an index strictly before the length of the left list, agrees with the defaulted reading of the left list.

The proof is by induction on the left list. The empty list admits no such index. For a cons cell, index 0 agrees by the two cons readings, and a successor index rewrites both readings and applies the inductive hypothesis after the lengths are compared.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic

@[expose] public section


namespace Domain.Recursive


/-- Choice-free `getD` of a left append. -/
theorem getD_append_cf {β : Type*} (l l' : List β) (d : β) :
    ∀ {n : ℕ}, n < l.length → (l ++ l').getD n d = l.getD n d := by
  induction l with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | cons a t ih =>
    intro n h
    cases n with
    | zero => rw [List.cons_append, List.getD_cons_zero, List.getD_cons_zero]
    | succ m =>
      rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (by rw [List.length_cons] at h; omega)

end Domain.Recursive
