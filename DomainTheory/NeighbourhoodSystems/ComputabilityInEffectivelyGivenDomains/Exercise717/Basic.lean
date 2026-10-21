/-ai
The pairing map relates a neighbourhood of the product of the sharp domain with itself to a neighbourhood of the sharp domain exactly when the source is the product of two sharp neighbourhoods whose paired embedding is contained in the target.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1Map
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.pairSharpMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1Map_rel

@[expose] public section

/-!
# Exercise 7.17 (Scott 1981, PRG-19, §7) — Part 1: all the Example 6.1 combinators for `D^§`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.17.** Complete the proof of 7.7 for showing that `D^§` is effectively given if `D` is.
> Include all the combinators of 6.1. Prove also that if `E` is effectively given and `u : D → E` and
> `v : E × E → E` are computable, then the unique strict mapping `g : D^§ → E`, where
> `g(in x) = u(x)` and `g(pair(y, z)) = v(g(y), g(z))`, is a computable mapping.

(Scott's text prints "6.2"; the construct `D^§` and its combinators are Example **6.1**, and 7.7 is
itself stated "all the combinators of Example 6.1", so we read it as 6.1.)

`Proposition77.dsharp_isEffectivelyGiven` already gives the first clause (`D^§` effectively given), and
`Combinators77.lean` did **a selection** of the combinators (`inSharp = λx. x^§`, and the pair-part
first projection `proj₀`). **This file finishes Part 1** — the *full* set of Example 6.1's algebra
combinators, each as an `ApproximableMap` that is `IsComputableMap` w.r.t. the canonical
presentation(s):

* **`proj1Map`** — the second projection of the pair part, `proj₁ : D^§ → D^§`
  (`proj1_toElementMap_pairSharp : proj₁(⟨x, y⟩^§) = y`); computable via the right-child reindex
  (`proj1_isComputable`). The exact mirror of `Combinators77.proj0Map`.
* **`pairSharpMap`** — Scott's pairing constructor `pair : D^§ × D^§ → D^§` as a joint approximable
  map out of the product `prod (D^§) (D^§)` (`pairSharpMap_toElementMap : pair(x, y) ↦ ⟨x, y⟩^§`,
  i.e. `Example61.pairSharp`); computable because its index relation is exactly
  `V_{2·⟨a,b⟩+2} ⊆ V_k` (`pairSharp_isComputable`), a recursive slice of `D^§`'s inclusion decider.

Together with `inSharpMap`/`proj0Map` this is the complete combinator set of the domain equation
`D^§ ≅ D + (D^§ × D^§)`: the two injections `in`, `pair` and the two pair-part projections.

The **second clause** of 7.17 (the universal strict catamorphism `g : D^§ → E` and its computability)
is a separate, larger development handled subsequently.

As in `Combinators77.lean`, all `ApproximableMap` **data** and the **faithfulness** theorems are
choice-free `⊆ {propext, Quot.sound}`; only the `IsComputableMap` proofs route through `Classical`
(set reasoning over the arbitrary carrier `α`, inherited from `incl_computable`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-! ### `proj₁ : D^§ → D^§` (second projection of the pair part). -/



/-! ### `pair : D^§ × D^§ → D^§` (Example 6.1's pairing constructor `⟨·, ·⟩^§`).

This is a *joint* combinator, so it is an approximable map out of the product `D^§ × D^§`. On the
product neighbourhood `A ∪ B` (over `α ⊕ α`) it returns `1·A ∪ 2·B` (= `embPair A B`); the master
input `Δ ∪ Δ` maps to `Γ` (since `embPair Γ Γ ⊆ Γ`). -/


@[simp] theorem pairSharpMap_rel {V : Set ((List Bool × α) ⊕ (List Bool × α))}
    {W : Set (List Bool × α)} :
    (pairSharpMap hD).rel V W ↔
      (prod (Dsharp D hD) (Dsharp D hD)).mem V ∧ MemS D W ∧
        ∃ A B, MemS D A ∧ MemS D B ∧ V = prodNbhd A B ∧ embPair A B ⊆ W := Iff.rfl
end Proposition77
end DomainTheory.NeighbourhoodSystems
