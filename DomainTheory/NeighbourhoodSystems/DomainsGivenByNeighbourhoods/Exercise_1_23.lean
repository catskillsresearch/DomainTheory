module

import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_13
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise123
section

open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

def state : ℕ → Set α × Set α
  | 0 => (enum 0, V.master ∩ enum 0)
  | (n + 1) =>
      if V.mem ((state n).2 ∩ enum (n + 1)) then
        (enum (n + 1), (state n).2 ∩ enum (n + 1))
      else
        state n

def Y (n : ℕ) : Set α := (state V enum n).1

@[simp] theorem Y_zero : Y V enum 0 = enum 0 := rfl

def acc (n : ℕ) : Set α := (state V enum n).2

@[simp] theorem acc_zero : acc V enum 0 = V.master ∩ enum 0 := rfl

abbrev cond (n : ℕ) : Prop := V.mem (acc V enum n ∩ enum (n + 1))

theorem state_succ (n : ℕ) :
    state V enum (n + 1) =
      if cond V enum n then (enum (n + 1), acc V enum n ∩ enum (n + 1)) else state V enum n :=
  rfl

theorem Y_succ_neg {n : ℕ} (h : ¬ cond V enum n) : Y V enum (n + 1) = Y V enum n := by
  show (state V enum (n + 1)).1 = (state V enum n).1
  rw [state_succ, ite_eq_right h]

theorem Y_succ_pos {n : ℕ} (h : cond V enum n) : Y V enum (n + 1) = enum (n + 1) := by
  show (state V enum (n + 1)).1 = enum (n + 1)
  rw [state_succ, ite_eq_left h]

theorem acc_succ_neg {n : ℕ} (h : ¬ cond V enum n) :
    acc V enum (n + 1) = acc V enum n := by
  show (state V enum (n + 1)).2 = (state V enum n).2
  rw [state_succ, ite_eq_right h]

theorem acc_succ_pos {n : ℕ} (h : cond V enum n) :
    acc V enum (n + 1) = acc V enum n ∩ enum (n + 1) := by
  show (state V enum (n + 1)).2 = acc V enum n ∩ enum (n + 1)
  rw [state_succ, ite_eq_left h]

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

section
variable (henum : ∀ n, V.mem (enum n))

include henum

theorem acc_mem : ∀ n, V.mem (acc V enum n) := by
  intro n
  induction n with
  | zero =>
    rw [acc_zero, Set.inter_eq_right.mpr (V.sub_master (henum 0))]
    exact henum 0
  | succ n ih =>
    by_cases h : cond V enum n
    · rw [acc_succ_pos V enum h]; exact h
    · rw [acc_succ_neg V enum h]; exact ih

include henum

theorem mem_interUpTo_Y : ∀ n, V.mem (V.interUpTo (Y V enum) n) := by
  intro n
  cases n with
  | zero => rw [interUpTo_zero]; exact V.master_mem
  | succ n => rw [← acc_eq_interUpTo V enum]; exact acc_mem V enum henum n
end
end

end DomainTheory.NeighbourhoodSystems.Exercise123

section
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise123
section

open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]
variable (henum : ∀ n, V.mem (enum n))

include henum

def greedyElement : V.Element where
  mem X := V.mem X ∧ ∃ n, V.interUpTo (Y V enum) n ⊆ X
  sub h := h.1
  master_mem := ⟨V.master_mem, 0, by rw [interUpTo_zero]⟩
  inter_mem := by
    rintro X X' ⟨hX, n, hn⟩ ⟨hX', m, hm⟩
    have hsub : V.interUpTo (Y V enum) (max n m) ⊆ X ∩ X' :=
      Set.subset_inter
        ((V.interUpTo_antitone (Y V enum) (le_max_left n m)).trans hn)
        ((V.interUpTo_antitone (Y V enum) (le_max_right n m)).trans hm)
    exact ⟨V.inter_mem hX hX' (mem_interUpTo_Y V enum henum (max n m)) hsub, max n m, hsub⟩
  up_mem := by
    rintro X X' ⟨_, n, hn⟩ hX' hsub
    exact ⟨hX', n, hn.trans hsub⟩
end

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

variable (henum : ∀ n, V.mem (enum n))
include henum

theorem Y_mem : ∀ n, V.mem (Y V enum n) := by
  intro n
  induction n with
  | zero => rw [Y_zero]; exact henum 0
  | succ n ih =>
    by_cases h : cond V enum n
    · rw [Y_succ_pos V enum h]; exact henum (n + 1)
    · rw [Y_succ_neg V enum h]; exact ih

theorem Y_prefix_consistent (n : ℕ) : V.Consistent (Y V enum) n :=
  ⟨V.interUpTo (Y V enum) n, mem_interUpTo_Y V enum henum n, subset_rfl⟩

theorem greedyElement_mem_Y (n : ℕ) : (greedyElement V enum henum).mem (Y V enum n) :=
  ⟨Y_mem V enum henum n, n + 1, V.interUpTo_subset (Y V enum) (Nat.lt_succ_self n)⟩

theorem greedyElement_mem_acc (n : ℕ) : (greedyElement V enum henum).mem (acc V enum n) := by
  refine ⟨acc_mem V enum henum n, n + 1, ?_⟩
  rw [acc_eq_interUpTo V enum]

variable (hsurj : ∀ {X : Set α}, V.mem X → ∃ n, enum n = X)
include hsurj

theorem greedyElement_isTotal : V.IsTotal (greedyElement V enum henum) := by
  intro z hz W hW
  obtain ⟨k, rfl⟩ := hsurj (z.sub hW)
  cases k with
  | zero =>
    have : Y V enum 0 = enum 0 := Y_zero V enum
    rw [← this]
    exact greedyElement_mem_Y V enum henum 0
  | succ m =>
    by_cases h : cond V enum m
    · have hYk : Y V enum (m + 1) = enum (m + 1) := Y_succ_pos V enum h
      rw [← hYk]
      exact greedyElement_mem_Y V enum henum (m + 1)
    · exfalso
      apply h
      have hacc_z : z.mem (acc V enum m) := hz _ (greedyElement_mem_acc V enum henum m)
      have : z.mem (acc V enum m ∩ enum (m + 1)) := z.inter_mem hacc_z hW
      exact z.sub this

omit [DecidablePred V.mem] in

theorem filters_sequence_determined (x : V.Element) :
    ∃ s : ℕ → Set α, (∀ n, V.mem (s n)) ∧ ∀ Z, x.mem Z ↔ (V.mem Z ∧ ∃ n, s n ⊆ Z) := by
  classical
  refine ⟨fun i => if x.mem (enum i) then enum i else V.master, ?_, ?_⟩
  · intro n
    by_cases h : x.mem (enum n)
    · simp only [ite_eq_left h]; exact henum n
    · simp only [ite_eq_right h]; exact V.master_mem
  · intro Z
    constructor
    · intro hZ
      obtain ⟨k, hk⟩ := hsurj (x.sub hZ)
      have hxk : x.mem (enum k) := by rw [hk]; exact hZ
      refine ⟨x.sub hZ, k, ?_⟩
      show (if x.mem (enum k) then enum k else V.master) ⊆ Z
      rw [ite_eq_left hxk]; exact hk.subset
    · rintro ⟨hZmem, n, hn⟩
      have hsx : x.mem (if x.mem (enum n) then enum n else V.master) := by
        by_cases h : x.mem (enum n)
        · simp only [ite_eq_left h]; exact h
        · simp only [ite_eq_right h]; exact x.master_mem
      exact x.up_mem hsx hZmem hn

end Exercise123

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise123
section

set_option linter.unusedVariables false

theorem example_123.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (enum : Nat → Set α)
  [inst : @DecidablePred (Set α) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V)],
  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (enum n)) →
    ∀ (n : Nat),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
        (@DomainTheory.NeighbourhoodSystems.Exercise123.Y α V enum inst) n :=
  @DomainTheory.NeighbourhoodSystems.Exercise123.Y_prefix_consistent
end

end DomainTheory.NeighbourhoodSystems.Exercise123
end
