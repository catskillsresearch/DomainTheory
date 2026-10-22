/-ai
The consistency bit of two fragment expressions is true if and only if the denotation of their intersection expression is nonempty.

Unfolding the definitions, the consistency bit is the nonemptiness bit of the intersection expression, and that bit is true exactly when the denotation is nonempty.

The intersection of the denotations of two expressions is nonempty if and only if their consistency bit is true.

The intersection of the denotations is the denotation of the intersection expression, and the previous equivalence applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autStateCard
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.toNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathAppend
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathAppend_take_drop
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.decideNonemptyB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.decideEmptyB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.consistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter_mem_eval_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.NFAinter_mem_accepts_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.dfaToNFA_eval
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.dfaToNFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.toNFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.mem_accepts_of_path
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.accepts_skip_loop
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.accepts_card_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.accepts_shorten_step
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.exists_accepted_word_short
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autStateCard_eq_card
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.denote_nonempty_iff_short
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.decideNonemptyB_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.decideEmptyB_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.BasicInst40
public meta import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public meta import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section

/-!
# Exercise 7.22 — every fragment expression has a `Fintype` automaton (`denote e = accepts`)

Assembles the leaf automata (`Exercise722DFA.lean`) and the concatenation automaton
(`Exercise722Cat.lean`) into a single uniform recogniser

  `toNFA : (e : SExpr) → NFA Bool (autState e)`     with     `toNFA_accepts : (toNFA e).accepts = denote e`

where the state type `autState e` is a `Fintype` (built from `Unit`, `Option (Fin _)`, `×`, `⊕`).
This is the constructive, **choice-free** realisation of Scott's "the sets in `S` are regular events":
every fragment language is the accepted language of an explicit finite automaton. It is the platform
for the emptiness/equivalence decision procedure (and hence Definition 7.1 effective givenness).

The missing combinator beyond the leaves+`cat` is intersection, handled here by the standard product
construction `NFAinter` (mathlib has `DFA.inter` but no `NFA` intersection).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}

/-! ## NFA intersection (product) -/

/-! ## Choice-free DFA → NFA recognition

mathlib's `DFA.toNFA_correct` depends on `Classical.choice`; we reprove it choice-free (the leaf
automata are DFAs, so the uniform `toNFA` must convert them without pulling choice). -/

/-! ## The uniform recogniser `toNFA` -/

example : DecidableEq (autState (.sigma : SExpr)) := inferInstance
example : DecidableEq (autState (.single [true, false] : SExpr)) := inferInstance

/-! ## Emptiness reduces to reachability of an accept state

Since the state space is a `Fintype`, this reduces Definition 7.1's relation (ii) — consistency,
which by positivity of `Ssys` (`Exercise722.lean`) is exactly `∩`-non-emptiness — to a **finite**
reachability question. The two clean routes to a primitive-recursive decider from here are flagged in
the module docstring of `Exercise722DFA.lean`. -/

variable {σ : Type}

/-! ## Short-word search (Session C4)

If an `n`-state NFA accepts some word, it accepts one of length `< n` (pigeonhole on a concrete
accepting path). This is tighter than mathlib's `NFA.pumping_lemma`, which bounds via `card (Set σ)`.
-/

/-! ## Emptiness decider (Session C5) -/

/-! ## Consistency decider (Session C6) — Definition 7.1 relation (ii)

For `X, Y ∈ S`, Scott's consistency `∃ Z ∈ S, Z ⊆ X ∩ Y` is equivalent to `(X ∩ Y).Nonempty`
by positivity (`Ssys_isPositive`). On syntax, this is non-emptiness of `denote (cap a b)`. -/

@[simp] theorem consistentB_iff (a b : SExpr) :
    consistentB a b = true ↔ (denote (.cap a b)).Nonempty := by
  have h : consistentB a b = decideNonemptyB (.cap a b) := by
    simp [consistentB, decideEmptyB, decideNonemptyB]
  rw [h, decideNonemptyB_iff]

@[simp] theorem capNonempty_iff_consistent (a b : SExpr) :
    (denote a ∩ denote b).Nonempty ↔ consistentB a b = true := by
  rw [← denote_cap, consistentB_iff]

/-! ## Relation (i) `interEq` — what `decideEmptyB` / `consistentB` do *not* decide (Session C7a)

**Definition 7.1 (i)** on an encoded presentation is the ternary relation
`Xₙ ∩ Xₘ = Xₖ`. On `SExpr` syntax this is *exactly regular-language equivalence*
(`interEq_iff` in `Exercise722Regular.lean`):

  `denote a ∩ denote b = denote k  ↔  denote (cap a b) = denote k`.

Relation (ii) consistency is now mechanised (`consistentB` / `decideEmptyB` on `cap a b`).
Relation (i) is **strictly harder**: it asks whether two *different* syntactic caps denote the
*same* language, not merely whether their intersection is empty.

**Why emptiness alone is insufficient.** The fragment is not closed under complement or set-difference
(`L₁ ⊆ L₂ ↔ L₁ \ L₂ = ∅` needs `\`). The concrete obstruction is `sigma_ne_containsZero`:
`denote .sigma ≠ denote containsZero` (witness `[true] ∈ Σ` but `[true] ∉ Σ·{0}·Σ`), yet no
fragment-emptiness query on `cap`/`cat`/`single`/`sigma` alone exposes this inequality — detecting
`Σ \ "contains 0"` needs the complement language `{1}*`, which is **not expressible** in the
fragment. Hence `decideEmptyB` and `consistentB` cannot decide (i).

**What a full (i) decider would need (Session C7b, DEFER).** Language equivalence
`denote e₁ = denote e₂` reduces to emptiness of the symmetric difference, hence to deciding
`(e₁ ∩ e₂ᶜ)` and `(e₂ ∩ e₁ᶜ)` — i.e. **complement** (`complDFA` exists) wired into a uniform
`toDFA` / product construction, or an alternative such as Myhill–Nerode bisimulation on the
`autState` types. Until C7b lands, `Ssys_partially_effectively_given` will carry (ii) only. -/
end Exercise722
end DomainTheory.NeighbourhoodSystems
