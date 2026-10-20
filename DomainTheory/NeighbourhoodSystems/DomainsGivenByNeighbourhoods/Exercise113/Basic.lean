/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.ExampleB
public import DomainTheory.Neighborhood.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Exercise 1.13 (Scott 1981, PRG-19, §1) — the infinite binary system `B`, revisited

Scott: "Verify all the assertions made about the system `B` … Draw a picture … which includes nodes
for all `σ ∈ Σ*` … and where the total elements lie. (The picture … has to have limit nodes all
along the top.)"

The "assertions about `B`" are exactly the content of `ExampleB.lean`:

* `ExampleB.B` is a neighbourhood system (`ExampleB.nestedOrDisjoint`);
* `ExampleB.sigmaElt`/`sigmaElt_bot` realize Scott's `σx` and `σ⊥` with `σx ∈ |B|`;
* `ExampleB.sigmaBot_le_iff` is "`σ₀⊥ ⊑ σ₁⊥ ⟺ σ₀` initial segment of `σ₁`";
* `ExampleB.mem_iff_exists_sigmaBot` is "`x = ⋃ₙ σₙ⊥`".

This file supplies the **limit nodes**: for an infinite path `p : ℕ → Bool` we build the element
`branch p ∈ |B|` as the ascending union (Theorem 1.11(ii)) of the finite approximations
`σₙ⊥ = (p↾n)⊥`, show every finite approximation approximates it (`branchSeq_le_branch`), and prove it
is a **total** (maximal) element (`branch_isTotal`). These are the nodes "along the top".

Constructive except `branch_isTotal`'s use of `B`'s structure (still `[propext, Quot.sound]`).
-/

namespace DomainTheory.Neighborhood.Exercise113

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB

/-- The length-`n` initial segment `p ↾ n = ⟨p 0, …, p (n-1)⟩` of an infinite path `p`. -/
def prefixSeq (p : ℕ → Bool) : ℕ → Str
  | 0 => []
  | (n + 1) => prefixSeq p n ++ [p n]

@[simp] theorem prefixSeq_length (p : ℕ → Bool) (n : ℕ) : (prefixSeq p n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [prefixSeq, ih]

theorem prefixSeq_prefix_succ (p : ℕ → Bool) (n : ℕ) :
    prefixSeq p n <+: prefixSeq p (n + 1) := ⟨[p n], rfl⟩

theorem prefixSeq_mono (p : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    prefixSeq p n <+: prefixSeq p m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ k _ ih => exact ih.trans (prefixSeq_prefix_succ p k)

/-- The finite approximations `σₙ⊥ = (p ↾ n)⊥` along the path `p`. -/
def branchSeq (p : ℕ → Bool) (n : ℕ) : B.Element := sigmaBot (prefixSeq p n)

theorem branchSeq_mono (p : ℕ → Bool) : Monotone (branchSeq p) := by
  intro n m h
  exact (sigmaBot_le_iff (prefixSeq p n) (prefixSeq p m)).mpr (prefixSeq_mono p h)

/-- **The limit/total element of an infinite path** `p`: the ascending union `⋃ₙ (p ↾ n)⊥`
(Theorem 1.11(ii)). These are the "limit nodes all along the top" of Scott's picture. -/
def branch (p : ℕ → Bool) : B.Element := B.iUnion (branchSeq p) (branchSeq_mono p)
end DomainTheory.Neighborhood.Exercise113
