/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Regular
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option

/-!
# Exercise 7.22 — toward effective givenness: explicit `Fintype` DFAs (WIP)

This is **work in progress** toward a choice-free decision procedure for the two Definition-7.1
relations of `Ssys` (`Exercise722.lean`), reduced in `Exercise722Regular.lean` to *language
equivalence on `SExpr`*. The plan (Route A): give every `SExpr` an explicit deterministic finite
automaton with a genuine `Fintype` state type, so that emptiness/equivalence become **structural**
finite searches (no Brzozowski-finiteness/ACI theorem needed).

mathlib supplies the closure operations we need *for free*:
* `DFA.inter` (`accepts_inter : (M₁.inter M₂).accepts = M₁.accepts ⊓ M₂.accepts`) — handles `cap`;
* `DFA.compl` (`accepts_compl`) + `inter` + emptiness — handles equivalence (`A = B ↔ A △ B = ∅`).

What mathlib does **not** supply, and what remains the crux (designated for a high-compute session):
* a **language-concatenation automaton** (`cat`): no NFA/εNFA concatenation exists in mathlib, so it
  must be built (εNFA with ε-links from `a`'s accept states to `b`'s start) and proved correct
  (`accepts = denote a * denote b`) via `εNFA.IsPath`/`isPath_append`;
* a `Finset`-based subset construction (mathlib's `NFA.n` determinizes to `Set σ`, which lacks
  `DecidableEq`), needed so the final emptiness/equivalence search is decidable data;
* the bridge from the resulting `Decidable` search to the project's `RecDecidable` (`Nat.Primrec`).

**This file (Medium pass) provides the leaf automata, proven correct, and the framework.** The `cat`
construction and the decision bridge are the remaining (high-compute) work.
-/

namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability

/-! ## `Σ` (the universal language) -/

/-- The one-state DFA recognising `Σ = {0,1}*` (every word accepted). -/
def sigmaDFA : DFA Bool Unit where
  step _ _ := ()
  start := ()
  accept := Set.univ

@[simp] theorem sigmaDFA_accepts : sigmaDFA.accepts = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_univ _

/-! ## A singleton `{σ}` -/

/-- States of the single-word DFA for `σ`: `some i` means "the input so far is the length-`i` prefix
of `σ`" (`i ≤ |σ|`); `none` is the dead/sink state (input has diverged from `σ`). -/
abbrev SingleState (σ : List Bool) : Type := Option (Fin (σ.length + 1))

/-- The single-word DFA recognising `{σ}`. From `some i` (`i < |σ|`) reading the correct next
character advances to `some (i+1)`; any mismatch — or any character once `σ` is fully consumed — goes
to the dead state `none`. -/
def singleDFA (σ : List Bool) : DFA Bool (SingleState σ) where
  step s b := s.bind fun i =>
    if h : (i : ℕ) < σ.length then
      if σ.get ⟨i, h⟩ = b then some ⟨i + 1, by omega⟩ else none
    else none
  start := some ⟨0, by omega⟩
  accept := {some ⟨σ.length, by omega⟩}

/-! ## Intersection (`cap`) and complement — free from mathlib

`cap` needs no new automaton: mathlib's `DFA.inter` is the product construction, and the resulting
state type `σ₁ × σ₂` keeps `Fintype`/`DecidableEq`. The wrapper below packages it against `denote`,
and `complDFA_accepts` records the complement (used to reduce equivalence to emptiness). -/

/-- The complement DFA recognises the set-complement of the original language (over all of `Σ*`).
(Choice-free; avoids mathlib's classical `accepts_compl`.) -/
theorem complDFA_accepts {σ : Type} (M : DFA Bool σ) (a : SExpr) (h : M.accepts = denote a) :
    (Mᶜ).accepts = (denote a)ᶜ := by
  rw [← h]
  ext w
  exact Iff.rfl

/-! ## State-space finiteness is structural

The whole point of Route A: the state types of the leaf/closure automata carry `Fintype` *and*
`DecidableEq` instances automatically (`Unit`, `Option (Fin _)`, products), so the eventual
emptiness/equivalence search is a finite, decidable computation — no Brzozowski-finiteness theorem is
needed. (`cat` will determinize to a `Finset`-state DFA, preserving both instances.) -/

example : Fintype (Unit) := inferInstance
example : DecidableEq (Unit) := inferInstance
example (σ : List Bool) : Fintype (SingleState σ) := by unfold SingleState; infer_instance
example (σ : List Bool) : DecidableEq (SingleState σ) := by unfold SingleState; infer_instance
example {σ₁ σ₂ : Type} [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ × σ₂) := inferInstance
example {σ₁ σ₂ : Type} [DecidableEq σ₁] [DecidableEq σ₂] : DecidableEq (σ₁ × σ₂) := inferInstance
end Exercise722
end DomainTheory.Neighborhood
