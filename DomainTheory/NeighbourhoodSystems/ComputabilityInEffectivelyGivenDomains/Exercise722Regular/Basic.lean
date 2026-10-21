/-ai
This file gathers and re-exports the syntax of expressions, their encoding and fuel-bounded decoding together with the round trip and the bound on the second component of a positive-tagged pair, denotation and the Boolean matcher with the matcher's correctness, the empty expression and the expression for words containing a zero, the four denotation equations, the split characterization of concatenation, and the instances of encodability, decidable membership, and countability.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Basic

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprToNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNatFuel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.matchesB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.emptyExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.containsZero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.snd_lt_pair_of_pos_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sexprOfNatFuel_sexprToNat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.mem_concat_iff_split
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.matchesB_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst16
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst17
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_emptyExpr

@[expose] public section

/-!
# Exercise 7.22 (Scott 1981, PRG-19, §7) — the regular-event layer

This file develops the **"regular events" hint** of Exercise 7.22 toward *effective givenness* of the
neighbourhood system `Ssys` of `Exercise722.lean`. Scott's hint:

> the sets in `S` are each "regular events" in the terminology of automata theory, and we have a
> decision method for the set algebra of regular events.

## What is mechanised here (green, choice-free)

We make the "regular event" content precise by giving `S` a finite **syntax** and a denotation, and
proving the syntax exactly captures `S`:

* `SExpr` — the syntax of `S`-terms: `Σ` (`sigma`), a singleton `{σ}` (`single σ`), concatenation
  `X·Y` (`cat`), and intersection `X ∩ Y` (`cap`). This is a *fragment* of regular expressions
  (closed under `·` and `∩`, with the universal language `Σ`), with **no** union, complement, or
  Kleene star — exactly Scott's four generators.
* `denote : SExpr → Set (List Bool)` — the language denoted by a term.
* **Decidable membership** `decide (w ∈ denote e)` via a `Bool` matcher `matchesB` with
  `matchesB_iff`, giving `DecidablePred (· ∈ denote e)` (choice-free). This is the computational core
  of "regular event": *membership of a word is decidable*.
* **Soundness/completeness**: `InS (denote e)` whenever `denote e` is non-empty
  (`InS_denote_of_nonempty`), and every member of `S` is a denotation (`InS_exists_denote`). Hence the
  exact characterization `InS X ↔ ∃ e, denote e = X ∧ X.Nonempty` (`inS_iff_exists_denote`).
* `SExpr` is countable (`Encodable SExpr`), so `S` is at most countable (Scott's standing finiteness).

## What remains for full effective givenness (Definition 7.1) — documented, not mechanised

Building a `ComputablePresentation`/`ScottPresentation Ssys` (Definition 7.1) requires Scott's two
relations to be **recursively decidable**, i.e. computed by genuine *primitive-recursive* functions
(`Domain.Recursive.RecDecidable = ∃ f, Nat.Primrec f ∧ …`); classical decidability does **not**
suffice. Over the syntax codes the two relations are:

* **(ii) consistency** `∃k. X_k ⊆ Xₙ ∩ Xₘ` ≡ (by positivity, Exercise 1.19 / `Ssys_isPositive`)
  **non-emptiness of `denote eₙ ∩ denote eₘ`** = non-emptiness of `denote (cap eₙ eₘ)`;
* **(i)** `Xₙ ∩ Xₘ = X_k` is **language equivalence** `denote (cap eₙ eₘ) = denote e_k`.

Both are decidable for regular events, but the decision procedures are **automata-complete**:

* *Emptiness* of an intersection genuinely needs the product-automaton reachability argument (there is
  no structural recursion for `∩`-emptiness: e.g. `Σ{0}Σ ∩ Σ{1}Σ` is non-empty while `{00} ∩ {11}`
  is empty), and a bounded-search emptiness test needs a *proven* state/length bound from a DFA.
* *Equivalence* is **not** reducible to intersection-emptiness inside this class, because the class is
  **not** closed under complement/difference (`L₁ ⊆ L₂ ⟺ L₁ \ L₂ = ∅` needs `\`). It requires a
  regular-language equivalence procedure (minimal DFAs / Myhill–Nerode, cf. `Example62Regular.lean`).

Mechanising those choice-free in `Recursive.lean` (a primitive-recursive subset construction +
reachability + a pumping/length bound, then `matchesB` over a bounded word set) is a separate, large
undertaking. Everything in *this* file is `⊆ {propext, Quot.sound}` (no `Classical.choice`).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-! ## Syntax and denotation -/

/- `deriving Encodable` builds a private auxiliary type, which a public instance cannot see.
This encoding is the public replacement: constructor tag in `Nat.pair`'s first component. -/


/-! ## Decidable word membership (the computational core of "regular event") -/


/-! ## Soundness and completeness: the syntax captures exactly `S` -/

/-! ## Countability of `S`

`SExpr` is built from `List Bool` by finitely many constructors, hence countable; so `S`, being the
range of `denote` (restricted to non-empty denotations), is at most countable — Scott's standing
"at most a countable infinity of neighbourhoods" (Definition 7.1). -/


/-! ## Reducing Definition 7.1's two relations to language equivalence on `SExpr`

The enumeration of `S` is (essentially) `n ↦ denote (decode n)` for codes `decode n : SExpr`. Over
such codes, Scott's two recursive-decidability obligations of Definition 7.1 become:

* **(ii)** consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` ≡ (positivity) `(denote eₙ ∩ denote eₘ).Nonempty`;
* **(i)** `Xₙ ∩ Xₘ = X_k` ≡ `denote (cap eₙ eₘ) = denote e_k`.

We show **both** are instances of *deciding language equivalence of two `SExpr`s* — and that emptiness
alone is therefore **not** enough (relation (i) needs the full equivalence test). -/


/-! ## Why an emptiness decider is *not* enough (the concrete obstruction)

Relation (i) is genuine regular-language **equivalence**, which is strictly stronger than
fragment-emptiness, because the fragment is **not closed under complement / set-difference**
(`L₁ ⊆ L₂ ↔ L₁ \ L₂ = ∅` needs `\`). The following exhibit the obstruction concretely. -/

end Exercise722
end DomainTheory.NeighbourhoodSystems
