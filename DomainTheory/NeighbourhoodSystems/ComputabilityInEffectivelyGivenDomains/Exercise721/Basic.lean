/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

/-!
# Exercise 7.21 (Scott 1981, PRG-19, §7) — combinators on the power domain

> **EXERCISE 7.21.** Is there a non-trivial combinator of type `ℙ(D → E) → (ℙD → ℙE)`?
> Are there in general any isomorphisms between the systems `(D → ℙE)`, `ℙ(D × E)`, `ℙD × ℙE`?
> Is there a non-trivial combinator of type `ℙ(D × E) × ℙ(E × F) → ℙ(D × F)`?
> Is there any connection between `ℙN` and `PN`?

This file answers the **first (headline) question with a full construction** and discusses the rest.

## The headline combinator `papply : ℙ(D → E) → (ℙD → ℙE)`

A `ℙ(D→E)`-neighbourhood `Φ` is a finite union of down-sets of *function-space* neighbourhoods; a
`ℙD`-neighbourhood `A` is a finite union of down-sets of `D`-neighbourhoods. The natural — and
non-trivial — combinator "applies a set of functions to a set of arguments" by collecting all the
applications. It is exactly the **Smyth power-domain lift of evaluation** (Theorem 3.11's
`eval : (D→E) × D → E`):

`papplyEval.rel Φ A B  :=  Φ ∈ ℙ(D→E) ∧ A ∈ ℙD ∧ B ∈ ℙE ∧ ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, G, X eval Y`,

the two-variable analogue of Exercise 7.19's `ℙf` (one level: `∀ X ∈ A, ∃ Y ∈ B, X f Y`) and of
Exercise 7.20's `union` (the nested `∀ ∀ ∃`). Packaged as the two-variable map `papplyEval`, made a
map out of the product `papplyB = ofMap₂ papplyEval : ℙ(D→E) × ℙD → ℙE`, and finally **curried**
(Theorem 3.12) to the *exact* type Scott asks for:

`papply = curry papplyB : ℙ(D→E) → (ℙD → ℙE)`.

It is **non-trivial**: `papplyEval_step_witness` exhibits, for any neighbourhoods `X₀ ∈ D`, `Y₀ ∈ E`,
the relation `↓[X₀,Y₀]  papply  ↓X₀ ↦ ↓Y₀` — the set of functions sending (at least) `X₀` to `Y₀`,
applied to (at least) `X₀`, yields (at least) `Y₀`. (Compare Exercise 7.19's image action
`ℙf({x,y}) = {f x, f x'}` — here the function is itself drawn from a power domain.)

## Computability (the implicit "if `D`, `E` effectively given" half)

*Yes, `papply` is computable whenever `eval` is.* Over the canonical presentations of Proposition
7.10 (`ℙ𝒟`-codes = finite lists of indices), the relation reduces (`papplyEval_rel_Ypd_iff`) to the
triply-nested bounded quantifier

`∀ g ∈ dl Φc, ∀ x ∈ dl Ac, ∃ y ∈ dl Bc, eval (Pf.X g) (P.X x) (Q.X y)`,

recursively enumerable (`papplyEval_isComputable`) because each layer preserves r.e.-ness: bounded
`∃` (`bExists_decodeList_re`, Ex 7.19) and parameterised bounded `∀`
(`REPred.forall_mem_decodeList₂`), assembled by the helper `re_forallG_forallX_existsY`. The base
predicate "`eval` is r.e. on codes" is precisely Theorem 7.5's `evalMap_isComputable` (transported to
the ternary relation through the function-space presentation `funPresentation`), so we take it as the
hypothesis `heval` — exactly as Exercise 7.19/7.20 take the component presentations as inputs.

## The other three questions (discussion)

* **Isomorphisms among `(D → ℙE)`, `ℙ(D × E)`, `ℙD × ℙE`?** *Not in general.* There are always
  canonical *maps* — e.g. `⟨ℙp₀, ℙp₁⟩ : ℙ(D×E) → ℙD × ℙE` (the Ex-7.19 functorial action of the two
  projections, paired) and a "graph/strength" map `D → ℙE` ↦ `ℙ(D×E)`-style — but none is an
  isomorphism for non-degenerate `D, E`. The Smyth power domain does **not** distribute over the
  product: `ℙ(D×E)` records *correlated* sets of pairs `{(d,e)}`, whereas `ℙD × ℙE` only records the
  two *marginals*; the map `ℙ(D×E) → ℙD × ℙE` forgets the correlation and is not injective on
  elements (e.g. `{(d₁,e₁),(d₂,e₂)}` and `{(d₁,e₂),(d₂,e₁)}` have the same marginals). Likewise
  `(D → ℙE)` (one set of outputs *per input*) carries strictly more information than a single
  `ℙ(D×E)`. So these are related by combinators, not isomorphisms, in general.
* **A combinator `ℙ(D × E) × ℙ(E × F) → ℙ(D × F)`?** *Yes* — **relational composition**, the Smyth
  lift of "compose the underlying relations": send sets `R ⊆ D×E`, `S ⊆ E×F` to
  `R ; S = {(d,f) ∣ ∃ e, (d,e) ∈ R ∧ (e,f) ∈ S}`. On neighbourhoods, `prodNbhd X Y ∈ R̄`,
  `prodNbhd Y' Z ∈ S̄` with `Y, Y'` consistent produce `prodNbhd X Z`; the middle witness `Y ∩ Y'`
  is gathered exactly as Exercise 7.19's choice-free `comp_witness`. It is the same recipe as
  `papply` (a binary Smyth lift), so "yes, and computable", and is not pursued in code here.
* **Connection between `ℙN` and `PN`?** Here `N` is the flat domain of naturals (Lecture VII's `𝒟 = N`)
  and `PN` is the powerset domain `𝒫(ℕ)` of Example 7.8. The Smyth power domain `ℙN` consists of the
  *finitely generated Smyth predicates* on `N`; its finite elements are finite sets of naturals
  (plus `⊥`), and the embedding "finite set ↦ its set of members" realises `ℙN` as the sub-domain of
  `PN` of finitely generated elements — `ℙN ⊴ PN` (Proposition 7.12's singleton/union machinery),
  with `PN` the ideal completion. They are *not* isomorphic (`PN` has uncountable elements, `ℙN`'s
  elements are the r.e./finite ones), but `ℙN` sits inside `PN` as its computable/finitary core.

## Axiom audit

As in Exercises 7.19/7.20, every declaration carries `Classical.choice`, but only at the `Prop` level
and only *inherited* from the power domain itself (Proposition 7.10's `PDmem_upSet_inter` `by_cases`,
used to build `PowerDomain`). The new content here — `papplyEval`, the displayed reduction, the r.e.
helper, and the curried combinator — adds **no further** use of choice; the recursion layer of
`Recursive.lean` is choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-! ### The combinator `papply` as the Smyth power-domain lift of `eval`. -/

/-- **Exercise 7.21 — the two-variable combinator `papplyEval : ℙ(D→E) × ℙD → ℙE`.** The Smyth
power-domain lift of evaluation (Theorem 3.11): a `ℙ(D→E)`-neighbourhood `Φ` applied to a
`ℙD`-neighbourhood `A` covers a `ℙE`-neighbourhood `B` iff every function-neighbourhood `G ∈ Φ`
applied to every argument-neighbourhood `X ∈ A` lands in some `Y ∈ B` (via `eval`, i.e. every
`f ∈ G` sends `X` into `Y`). This is the two-variable analogue of Exercise 7.19's `ℙf`. -/
def papplyEval (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap₂ (funSpace V W).PowerDomain V.PowerDomain W.PowerDomain where
  rel Φ A B := (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
    ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := by
    refine ⟨(funSpace V W).PDmem_master, V.PDmem_master, W.PDmem_master, ?_⟩
    intro G hG X hX
    simp only [mem_upSet] at hG hX
    refine ⟨W.master, ⟨W.master_mem, subset_rfl⟩, ?_⟩
    exact ⟨hG.1, hX.1, W.master_mem,
      fun f hf => f.mono f.master_rel (V.sub_master hX.1) subset_rfl hX.1 W.master_mem⟩
  inter_right := by
    rintro Φ A B B' ⟨hΦ, hA, hB, hbody⟩ ⟨-, -, hB', hbody'⟩
    refine ⟨hΦ, hA, W.PDmem_inter hB hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G hG X hX
    obtain ⟨Y', hY'B', hrel'⟩ := hbody' G hG X hX
    have hinmem : W.mem (Y ∩ Y') := (eval V W).rel_cod ((eval V W).inter_right hrel hrel')
    exact ⟨Y ∩ Y', Set.mem_inter
      (W.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (W.PDmem_down hB' hY'B' Set.inter_subset_right hinmem),
      (eval V W).inter_right hrel hrel'⟩
  mono := by
    rintro Φ Φ' A A' B B' ⟨_, _, _, hbody⟩ hΦ'Φ hA'A hBB' hΦ' hA' hB'
    refine ⟨hΦ', hA', hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G (hΦ'Φ hG) X (hA'A hX)
    exact ⟨Y, hBB' hYB, hrel⟩

@[simp] theorem papplyEval_rel {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {Φ : Set (Set (ApproximableMap V W))} {A : Set (Set α)} {B : Set (Set β)} :
    (papplyEval V W).rel Φ A B ↔ (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
      ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y := Iff.rfl

/-- **Exercise 7.21 — the combinator as a map out of the product `ℙ(D→E) × ℙD → ℙE`.** -/
def papplyB (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V W).PowerDomain V.PowerDomain) W.PowerDomain :=
  ofMap₂ (papplyEval V W)

/-- **Exercise 7.21 — the headline combinator `papply : ℙ(D→E) → (ℙD → ℙE)`.** Currying `papplyB`
(Theorem 3.12) gives the combinator of *exactly* the type Scott asks for. -/
def papply (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W).PowerDomain (funSpace V.PowerDomain W.PowerDomain) :=
  curry (papplyB V W)

/-! ### Computability: `papply` is computable whenever `eval` is.

The base predicate "`eval` is recursively enumerable on codes" is Theorem 7.5's `evalMap_isComputable`
transported to the ternary `eval` relation; we take it as the hypothesis `heval`. -/
end DomainTheory.NeighbourhoodSystems
