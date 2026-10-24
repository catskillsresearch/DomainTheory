module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem_1_11

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise113
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/- concordance: source L454 EXERCISE 1.13 infinite binary tree -/
/-- **Exercise 1.13 (total elements).** Each infinite path `p` gives a *total* (maximal) element
`branch p`: any `y` it approximates approximates it back. (These maximal elements are exactly the
limit nodes along the top of the binary-tree picture.) -/
theorem branch_isTotal (p : ℕ → Bool) : B.IsTotal (branch p) := by
  intro y hy X hX
  obtain ⟨σ, rfl⟩ := y.sub hX
  have hk : y.mem (cone (prefixSeq p σ.length)) :=
    hy _ ((branch_mem_iff p).mpr ⟨σ.length, List.prefix_rfl⟩)
  rcases prefix_comparable_of_mem y hX hk with h | h
  · exact (branch_mem_iff p).mpr ⟨σ.length, h⟩
  · have hlen : (prefixSeq p σ.length).length = σ.length := prefixSeq_length p σ.length
    have hσ : prefixSeq p σ.length = σ := h.eq_of_length hlen
    exact (branch_mem_iff p).mpr ⟨σ.length, by rw [hσ]⟩

section
set_option linter.unusedVariables false

theorem example_113 : ∀ (p : Nat → Bool),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal DomainTheory.NeighbourhoodSystems.ExampleB.Str
    DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise113.branch p) :=
  DomainTheory.NeighbourhoodSystems.Exercise113.branch_isTotal
end
end

end DomainTheory.NeighbourhoodSystems.Exercise113
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `⋂ₙ xₙ` is the **greatest** lower bound: anything approximating all `xₙ` approximates `⋂ₙ xₙ`. -/
theorem le_iInter (x : ℕ → V.Element) (y : V.Element) (h : ∀ n, y ≤ x n) :
    y ≤ V.iInter x :=
  fun X hX n => h n X hX

/-- `xₙ ⊑ ⋃ₙ xₙ`: every member of the sequence approximates the union. -/
theorem le_iUnion (x : ℕ → V.Element) (hmono : Monotone x) (n : ℕ) :
    x n ≤ V.iUnion x hmono :=
  fun _ hX => ⟨n, hX⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise113
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Every finite approximation `(p ↾ n)⊥` approximates the limit element `branch p`. -/
theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n
end

end DomainTheory.NeighbourhoodSystems.Exercise113
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is antitone in its length: a longer prefix is contained in a shorter
one. -/
theorem interUpTo_antitone (X : ℕ → Set α) {j k : ℕ} (h : j ≤ k) :
    V.interUpTo X k ⊆ V.interUpTo X j := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact Set.inter_subset_left.trans (ih (Nat.lt_succ_iff.mp h'))
end

end NeighborhoodSystem
namespace Exercise123
section

open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- Greedy *state*: `state n = (Yₙ, ⋂_{i≤n} Yᵢ)`. The running intersection in the second
component lets the consistency test `V.mem (acc ∩ enum (n+1))` be self-contained (Theorem 1.1c:
the prefix `Y₀,…,Yₙ,enum (n+1)` is consistent iff this intersection is a neighbourhood). -/
def state : ℕ → Set α × Set α
  | 0 => (enum 0, V.master ∩ enum 0)
  | (n + 1) =>
      if V.mem ((state n).2 ∩ enum (n + 1)) then
        (enum (n + 1), (state n).2 ∩ enum (n + 1))
      else
        state n

/-- The greedy sequence `Yₙ = (state n).1`. -/
def Y (n : ℕ) : Set α := (state V enum n).1

@[simp] theorem Y_zero : Y V enum 0 = enum 0 := rfl

/-- The running intersection `acc n = ⋂_{i≤n} Yᵢ = (state n).2`. -/
def acc (n : ℕ) : Set α := (state V enum n).2

@[simp] theorem acc_zero : acc V enum 0 = V.master ∩ enum 0 := rfl

/-- The consistency test at stage `n+1`: is `enum (n+1)` consistent with the prefix `Y₀,…,Yₙ`?
An `abbrev` so the `[DecidablePred V.mem]` instance is found through it. -/
abbrev cond (n : ℕ) : Prop := V.mem (acc V enum n ∩ enum (n + 1))

/-- The defining equation of `state` at a successor, written with the named `cond`/`acc`. -/
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

section
variable (henum : ∀ n, V.mem (enum n))

include henum

/-- The running intersection `acc n` is always a neighbourhood — the greedy choice guarantees it.
This is the content of Scott's hint (consistency of the prefix). -/
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

/-- `⋂_{i<n} Yᵢ` is always a neighbourhood. -/
theorem mem_interUpTo_Y : ∀ n, V.mem (V.interUpTo (Y V enum) n) := by
  intro n
  cases n with
  | zero => rw [interUpTo_zero]; exact V.master_mem
  | succ n => rw [← acc_eq_interUpTo V enum]; exact acc_mem V enum henum n
end
end

end Exercise123

end DomainTheory.NeighbourhoodSystems
end
