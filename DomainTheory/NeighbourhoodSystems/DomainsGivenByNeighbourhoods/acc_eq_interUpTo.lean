/-ai
The running intersection at stage n equals the intersection of the first n + 1 terms of the greedy sequence.

Proceed by induction on n. At zero, rewrite by the zero law of the running intersection, the successor and zero laws of the prefix intersection, and the zero law of the greedy sequence. At a successor, rewrite the prefix intersection by its successor law and apply the inductive hypothesis. When the condition holds, rewrite by the positive successor laws of the running intersection and of the greedy sequence. When the condition fails, rewrite by the negative successor laws. The inductive hypothesis identifies the running intersection with the prefix intersection, which is contained in the term at n, and that inclusion absorbs the extra intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_succ_neg
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_neg

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- `acc n = ⋂_{i<n+1} Yᵢ`: the carried intersection is exactly the prefix intersection. -/
theorem acc_eq_interUpTo : ∀ n, acc V enum n = V.interUpTo (Y V enum) (n + 1) := by
  intro n
  induction n with
  | zero =>
    rw [acc_zero, interUpTo_succ, interUpTo_zero, Y_zero]
  | succ n ih =>
    rw [interUpTo_succ, ← ih]
    by_cases h : cond V enum n
    · rw [acc_succ_pos V enum h, Y_succ_pos V enum h]
    · rw [acc_succ_neg V enum h, Y_succ_neg V enum h]
      have hsub : acc V enum n ⊆ Y V enum n := by
        rw [ih]; exact V.interUpTo_subset (Y V enum) (Nat.lt_succ_self n)
      rw [Set.inter_eq_left.mpr hsub]

end Exercise123

end DomainTheory.NeighbourhoodSystems
