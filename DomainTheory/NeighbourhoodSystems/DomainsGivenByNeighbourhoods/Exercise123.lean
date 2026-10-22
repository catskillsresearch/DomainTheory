module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.greedyElement
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_antitone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cond
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.state_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Y_succ_neg
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_pos
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_succ_neg
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_eq_interUpTo
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_interUpTo_Y

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


end NeighborhoodSystem

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]


variable (henum : ∀ n, V.mem (enum n))
include henum

/-- Each `Yₙ` is a neighbourhood. -/
theorem Y_mem : ∀ n, V.mem (Y V enum n) := by
  intro n
  induction n with
  | zero => rw [Y_zero]; exact henum 0
  | succ n ih =>
    by_cases h : cond V enum n
    · rw [Y_succ_pos V enum h]; exact henum (n + 1)
    · rw [Y_succ_neg V enum h]; exact ih


/-- **Exercise 1.23 — the hint.** For every `n`, the prefix `Y₀, …, Y_{n-1}` is consistent in
`𝒟`: its finite intersection is a neighbourhood, so it is its own common lower bound. -/
theorem Y_prefix_consistent (n : ℕ) : V.Consistent (Y V enum) n :=
  ⟨V.interUpTo (Y V enum) n, mem_interUpTo_Y V enum henum n, subset_rfl⟩


/-- Every `Yₙ` belongs to the greedy element. -/
theorem greedyElement_mem_Y (n : ℕ) : (greedyElement V enum henum).mem (Y V enum n) :=
  ⟨Y_mem V enum henum n, n + 1, V.interUpTo_subset (Y V enum) (Nat.lt_succ_self n)⟩

/-- The running intersection `acc n` belongs to the greedy element. -/
theorem greedyElement_mem_acc (n : ℕ) : (greedyElement V enum henum).mem (acc V enum n) := by
  refine ⟨acc_mem V enum henum n, n + 1, ?_⟩
  rw [acc_eq_interUpTo V enum]

variable (hsurj : ∀ {X : Set α}, V.mem X → ∃ n, enum n = X)
include hsurj

/-- **Exercise 1.23 — `{Yₙ}` is a total element.** Maximality: if `z` extends the greedy element
and `W ∈ z`, write `W = enum k` (surjectivity). For `k = 0`, `W = Y₀` is already in the greedy
element. For `k = m+1`: either the greedy step *accepted* `enum k` (then `W = Y_k` is in the
element), or it *rejected* it — but then `acc m ∩ enum k ∉ 𝒟`, contradicting that both `acc m`
(in the greedy element, hence in `z`) and `W` lie in the filter `z`. -/
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
/-- **Exercise 1.23 — "all filters can be determined by sequences".** In a countable system, every
filter `x` is the *limit family* of a sequence of neighbourhoods: take `sₙ = enum n` whenever
`enum n ∈ x` and `sₙ = Δ` otherwise. Every member of `x` is some `enum k` (surjectivity), so it is
caught by `s`; conversely each `sₙ ∈ x`, so anything above some `sₙ` is in `x`. (Classical: it
selects the sequence by deciding membership in `x`.) -/
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

set_option linter.unusedVariables false

theorem example_123.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (enum : Nat → Set α)
  [inst : @DecidablePred (Set α) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V)],
  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (enum n)) →
    ∀ (n : Nat),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
        (@DomainTheory.NeighbourhoodSystems.Exercise123.Y α V enum inst) n :=
  @DomainTheory.NeighbourhoodSystems.Exercise123.Y_prefix_consistent

end DomainTheory.NeighbourhoodSystems.Exercise123
