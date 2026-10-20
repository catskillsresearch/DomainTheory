/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise722Decide

@[expose] public section

/-!
# Exercise 7.22k — language equivalence via a `Finset`-valued subset construction (Session C7b)

`toNFA e : NFA Bool (autState e)` is genuinely nondeterministic once `.cat` is involved (the
concatenation automaton's ε-closure fans a single state out to several live states), so deciding
`denote e₁ = denote e₂` cannot be reduced to a simple bounded search over `matchesB` alone:
"`e₂` rejects `w`" is a *universal* statement over `e₂`'s nondeterministic paths, and universal
statements over NFA paths don't pump the way existential ones do (`exists_accepted_word_short`).

The fix is a **choice-free `Finset`-valued subset-construction simulation** of `toNFA e`: track the
*entire* set of live NFA states as a `Finset (autState e)` (decidable, since `autState e` already
carries `Fintype`/`DecidableEq`, `Exercise722Decide.lean`), evolving **deterministically**. Once
both `e₁`'s and `e₂`'s live-state-sets are tracked simultaneously (as one `Finset`-pair state), the
question "is there a word `e₁` accepts but `e₂` rejects" becomes an ordinary NFA-emptiness question
on a *deterministic* (singleton-step) NFA, to which `exists_accepted_word_short` applies directly.
-/

namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

/-! ## `Finset`-valued simulation of `toNFA e`

`acceptFin`/`startFin`/`stepFinSingle` mirror `toNFA`'s own recursive cases exactly, computing the
same sets as `Finset`s (decidable data) instead of `Set`s. Correctness (`coe_acceptFin` etc.) shows
each agrees with `toNFA e`'s actual `Set`-valued semantics. -/

/-- The accept states of `toNFA e`, as a `Finset`. -/
def acceptFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)}
  | .cap a b => (acceptFin a) ×ˢ (acceptFin b)
  | .cat a b => (acceptFin b).image (inr : autState b → autState a ⊕ autState b)

theorem coe_acceptFin : ∀ e : SExpr, (↑(acceptFin e) : Set (autState e)) = (toNFA e).accept
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.accept
      show (↑(Finset.univ : Finset Unit) : Set Unit) = Set.univ
      ext x; cases x; simp
  | .single σ => by
      change (↑({(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)} : Finset _) : Set _)
        = (singleDFA σ).toNFA.accept
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      change (↑((acceptFin a) ×ˢ (acceptFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).accept
      rw [Finset.coe_product, coe_acceptFin a, coe_acceptFin b]
      rfl
  | .cat a b => by
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.accept
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = inr '' (toNFA b).accept
      rw [Finset.coe_image, coe_acceptFin b]

/-- The start states of `toNFA e`, as a `Finset`. The `.cat` case handles the one-hop
ε-closure directly (`catEps`'s only ε-edges go from an `M₁`-accept state to `M₂`-start states,
`catEps_mem_εClosure_iff`): if some start state of `a` is already accepting, `b`'s start states
are also immediately live. -/
def startFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)}
  | .cap a b => (startFin a) ×ˢ (startFin b)
  | .cat a b =>
      if ((startFin a) ∩ (acceptFin a)).Nonempty
      then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
        (startFin b).image (inr : autState b → autState a ⊕ autState b)
      else (startFin a).image (inl : autState a → autState a ⊕ autState b)

/-- The step function of `toNFA e` from a single state, as a `Finset`. The `.cat` case's `inl`
branch mirrors `startFin`'s epsilon-closure handling exactly (one hop, on reaching an `a`-accept
state after the step). -/
def stepFinSingle : (e : SExpr) → autState e → Bool → Finset (autState e)
  | .sigma => fun _ _ => Finset.univ
  | .single σ => fun s c => {(singleDFA σ).step s c}
  | .cap a b => fun s c => (stepFinSingle a s.1 c) ×ˢ (stepFinSingle b s.2 c)
  | .cat a b => fun s c =>
      match s with
      | inl s' =>
          if ((stepFinSingle a s' c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b)
      | inr s' => (stepFinSingle b s' c).image (inr : autState b → autState a ⊕ autState b)

/-- The `Finset`-lifted step (mirrors `NFA.stepSet`). -/
def stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) : Finset (autState e) :=
  S.biUnion (fun s => stepFinSingle e s c)

/-- The live-state `Finset` after reading `w` (mirrors `NFA.eval`, folding `stepFin` left to
right from `startFin`). -/
def evalFin (e : SExpr) (w : List Bool) : Finset (autState e) :=
  w.foldl (stepFin e) (startFin e)

/-! ## The "difference" automaton: `e₁` is live and `e₂` is dead

Tracks `e₁`'s and `e₂`'s live-state `Finset`s *simultaneously* as one deterministic (singleton
step/start) NFA, so `exists_accepted_word_short` — genuinely generic over any `Fintype` NFA state
space — bounds the length of a shortest word witnessing `denote e₁ ⊄ denote e₂`. -/

/-- Tracks `(evalFin e₁ w, evalFin e₂ w)` deterministically; accepts `w` iff `e₁` is live-accepting
and `e₂` is not — i.e. `w ∈ denote e₁ \ denote e₂`. -/
def diffNFA (e1 e2 : SExpr) : NFA Bool (Finset (autState e1) × Finset (autState e2)) where
  step S c := {(stepFin e1 S.1 c, stepFin e2 S.2 c)}
  start := {(startFin e1, startFin e2)}
  accept := {S | (S.1 ∩ acceptFin e1).Nonempty ∧ S.2 ∩ acceptFin e2 = ∅}

/-! ## Bounded-word-search deciders for `⊆` and `=` -/

/-- `denote e₁ ⊆ denote e₂`, decided by a bounded search: if no word up to the `diffNFA` state
bound witnesses `e₁ \ e₂`, none exists at all (`exists_diff_word_short`). -/
def subsetB (e1 e2 : SExpr) : Bool :=
  (wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2)))).all
    (fun w => !matchesB e1 w || matchesB e2 w)

/-- **Exercise 7.22k.** Relation (i) on `SExpr` syntax — language equivalence — decided by
`subsetB` in both directions. -/
def interEqB (e1 e2 : SExpr) : Bool := subsetB e1 e2 && subsetB e2 e1
end Exercise722
end DomainTheory.Neighborhood
