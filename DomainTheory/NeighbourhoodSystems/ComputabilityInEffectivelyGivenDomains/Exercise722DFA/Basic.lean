/-ai
If a deterministic automaton accepts the denotation of an expression, its complement automaton accepts the complement of that denotation.

Cancel the hypothesis and compare membership. Acceptance by the complement automaton is definitionally failure of acceptance by the original automaton.

The unit type is finite, and equality of its elements is decidable. The state type of the single-word automaton is finite, and equality of its states is decidable. A product of finite types is finite, and a product of types with decidable equality has decidable equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.singleDFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.sigmaDFA_accepts
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.SingleState

@[expose] public section

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

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

/-! ## `Σ` (the universal language) -/


/-! ## A singleton `{σ}` -/


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
end DomainTheory.NeighbourhoodSystems
