module

public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Data.Set.Defs

@[expose] public section

section
universe u
namespace DomainTheory.NeighbourhoodSystems

structure PeanoModel (N : Type u) where

  zero : N

  succ : N → N

  zero_ne_succ : ∀ n, zero ≠ succ n

  succ_injective : Function.Injective succ

  induction : ∀ (s : Set N), zero ∈ s → (∀ n ∈ s, succ n ∈ s) → ∀ n, n ∈ s

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}

inductive Graph (P : PeanoModel M) (Q : PeanoModel N) : M → N → Prop
  | base : Graph P Q P.zero Q.zero
  | step : ∀ {m n}, Graph P Q m n → Graph P Q (P.succ m) (Q.succ n)

theorem Graph.swap {P : PeanoModel M} {Q : PeanoModel N} {m : M} {n : N}
    (h : Graph P Q m n) : Graph Q P n m := by
  induction h with
  | base => exact Graph.base
  | step _ ih => exact Graph.step ih

theorem graph_succ_right (P : PeanoModel M) (Q : PeanoModel N) {m : M} {k : N}
    (h : Graph P Q (P.succ m) k) : ∃ n, Graph P Q m n ∧ k = Q.succ n := by
  generalize hz : P.succ m = z at h
  cases h with
  | base => exact absurd hz.symm (P.zero_ne_succ _)
  | step h' =>
    rename_i m0 n0
    have hm : m = m0 := P.succ_injective hz
    subst hm
    exact ⟨n0, h', rfl⟩

theorem graph_zero_right (P : PeanoModel M) (Q : PeanoModel N) {k : N}
    (h : Graph P Q P.zero k) : k = Q.zero := by
  generalize hz : P.zero = z at h
  cases h with
  | base => rfl
  | step _ => exact absurd hz (P.zero_ne_succ _)

theorem exists_unique_right (P : PeanoModel M) (Q : PeanoModel N) (m : M) :
    ∃! n, Graph P Q m n := by
  refine P.induction {m | ∃! n, Graph P Q m n} ?_ ?_ m
  · exact ⟨Q.zero, Graph.base, fun k hk => graph_zero_right P Q hk⟩
  · rintro m' ⟨n', hn', huniq⟩
    refine ⟨Q.succ n', Graph.step hn', fun k hk => ?_⟩
    obtain ⟨n'', hn'', rfl⟩ := graph_succ_right P Q hk
    rw [huniq n'' hn'']

theorem exists_unique_left (P : PeanoModel M) (Q : PeanoModel N) (n : N) :
    ∃! m, Graph P Q m n := by
  obtain ⟨m, hm, huniq⟩ := exists_unique_right Q P n
  exact ⟨m, hm.swap, fun y hy => huniq y hy.swap⟩

end PeanoModel
end
end DomainTheory.NeighbourhoodSystems
end
