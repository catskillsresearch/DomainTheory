/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise619
public import DomainTheory.Neighborhood.Definition613
public import DomainTheory.Neighborhood.Exercise213
public import DomainTheory.Neighborhood.FunctionSpace

@[expose] public section

/-!
# Exercise 6.19 (Scott 1981, PRG-19, §6) — Part B: the functor algebra

> … Now generate all constructs `T(X)` formed by the constants (that is, `T(X) = 𝒟` for a fixed `𝒟`),
> by the identity (`T(X) = X`), and by sums and products (`T₀(X) + T₁(X)`, etc.). Show that these are
> all functors, continuous on maps, and monotone and continuous on domains.

This module formalizes **Part B**: the closed family of constructs `T(X)` over Scott's *uniform*
category of Exercise 6.19 — neighbourhood systems on `Δ ⊆ {0,1}*` with `∅ ∉ 𝒟` (the standing
hypothesis that makes the token-level sum `sumTok`/product `prodTok` of Part A genuine
*endo*-operations) and **strict** approximable maps.

## Contents

* `ScottSys` — an object of Scott's category: an `∅`-free neighbourhood system over `Str = {0,1}*`.
* The object actions `ScottSys.sum`/`ScottSys.prod` (Part A's `sumTok`/`prodTok`, repackaged so they
  stay inside the category) and the constant/identity objects.
* The **functorial action on maps**: `sumMapTok f₀ f₁ : (𝒟₀+𝒟₁) → (ℰ₀+ℰ₁)` and
  `prodMapTok f₀ f₁ : (𝒟₀×𝒟₁) → (ℰ₀×ℰ₁)`, each an approximable map, with strictness preservation
  (`sumMapTok` is *always* strict; `prodMapTok` is strict when both factors are).
* The **bifunctor laws**: both actions preserve identities and composition
  (`sumMapTok_id`/`sumMapTok_comp`, `prodMapTok_id`/`prodMapTok_comp`).
* The functor-expression algebra `FExpr` (constants, identity, sum, product), its object action
  `FExpr.obj`, its action on maps `FExpr.map`.

Scott asks to show these constructs are **all functors, continuous on maps, and monotone and
continuous on domains**; each is established here:

* **functors** — `FExpr.map_id` (`T(I)=I`) and `FExpr.map_comp` (`T(g∘f)=T(g)∘T(f)`), by induction;
  plus `FExpr.map_isStrict` (so `T` restricts to Scott's strict-map category).
* **continuous on maps** — `FExpr.map_mono` (a sharper map gives a sharper image) and
  `FExpr.map_continuous` (`λf. T(f)` preserves directed unions of maps); together these are exactly
  approximability of `λf. T(f)` (Exercise 2.13).
* **monotone on domains** — `FExpr.obj_subsystem` (`D ◁ E ⟹ T(D) ◁ T(E)`).
* **continuous on domains** — `FExpr.obj_continuous` (`λD. T(D)` preserves directed unions of
  subsystems, the form Scott uses in Theorem 6.14).

Because every construct stays over the single token type `{0,1}*`, the subdomain relation `◁` is
between systems on a common carrier, so the domain conditions need no carrier transport (unlike the
universe-polymorphic `Endofunctor DomainObj` form of Definitions 6.8/6.13).

This module also formalizes **Exercise 6.20**: writing `tok(𝒟) = 𝒟.master` for the underlying token
set and `{Γ}` for the one-neighbourhood system `singletonSys Γ`, the function `λΓ. tok(T({Γ}))` is
computed by the token-level recursion `mFun T` (`mFun_eq_master`), shown monotone (`mFun_mono`) and
continuous (`mFun_continuous`) on the domain `{Γ ∣ Λ ∈ Γ}`. Its least fixed point — the explicit
Kleene union `⋃ₙ mFunⁿ({Λ})` — gives a `Γ = tok(T({Γ}))` (`exists_tok_fixedPoint`), whence
`{Γ} ◁ T({Γ})` (`exists_singleton_subsystem`), exactly the hypothesis Theorem 6.14 needs.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

/-! ## Objects of Scott's category: `∅`-free systems over `{0,1}*` -/

/-- **An object of the Exercise 6.19 category.** An `∅`-free neighbourhood system over
`Str = {0,1}*` (`ne`: every neighbourhood is non-empty, Scott's `∅ ∉ 𝒟`). -/
structure ScottSys where
  /-- The underlying neighbourhood system on `{0,1}*`. -/
  sys : NeighborhoodSystem Str
  /-- `∅ ∉ 𝒟`: every neighbourhood is non-empty. -/
  ne : ∀ X, sys.mem X → X.Nonempty

/-- The **sum object** `𝒟₀ + 𝒟₁` of Part A, repackaged as an object of the category. -/
def ScottSys.sum (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨sumTok A₀.sys A₁.sys A₀.ne A₁.ne, sumTok_nonempty⟩

/-- The **product object** `𝒟₀ × 𝒟₁` of Part A, repackaged as an object of the category. -/
def ScottSys.prod (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨prodTok A₀.sys A₁.sys, prodTok_nonempty⟩

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- A non-empty `b`-tagged copy can never sit inside a `b'`-tagged copy for `b ≠ b'`. -/
theorem embBit_not_subset_cross {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty)
    (hsub : embBit b X ⊆ embBit b' Y) : False := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨w', he, -⟩ := hsub ⟨t, rfl, ht⟩
  simp only [List.cons.injEq] at he
  exact h he.1

/-! ## The functorial action of sum on maps -/

/-- **`f₀ + f₁`, the action of the sum functor on (approximable) maps.** It carries the master to the
master (so it is strict), a left copy `0X` to `0X'` whenever `X f₀ X'`, and a right copy `1Y` to
`1Y'` whenever `Y f₁ Y'`. -/
def sumMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.sum A₁).sys (B₀.sum B₁).sys where
  rel W W' :=
    ((sumTok A₀.sys A₁.sys A₀.ne A₁.ne).mem W ∧ W' = sumTokMaster B₀.sys B₁.sys) ∨
    (∃ X X', f₀.rel X X' ∧ W = embBit false X ∧ W' = embBit false X') ∨
    (∃ Y Y', f₁.rel Y Y' ∧ W = embBit true Y ∧ W' = embBit true Y')
  rel_dom := by
    rintro W W' (⟨hW, -⟩ | ⟨X, X', hrel, rfl, -⟩ | ⟨Y, Y', hrel, rfl, -⟩)
    · exact hW
    · exact Or.inr (Or.inl ⟨X, f₀.rel_dom hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, f₁.rel_dom hrel, rfl⟩)
  rel_cod := by
    rintro W W' (⟨-, rfl⟩ | ⟨X, X', hrel, -, rfl⟩ | ⟨Y, Y', hrel, -, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X', f₀.rel_cod hrel, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y', f₁.rel_cod hrel, rfl⟩)
  master_rel := Or.inl ⟨(A₀.sum A₁).sys.master_mem, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ h1 h2
    rcases h1 with ⟨hW, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · rcases h2 with ⟨-, rfl⟩ | ⟨X, X', hrel, hWeq, rfl⟩ | ⟨Y, Y', hrel, hWeq, rfl⟩
      · exact Or.inl ⟨hW, by rw [Set.inter_self]⟩
      · exact Or.inr (Or.inl ⟨X, X', hrel, hWeq, by rw [sumTokMaster_inter_embF (f₀.rel_cod hrel)]⟩)
      · exact Or.inr (Or.inr ⟨Y, Y', hrel, hWeq, by rw [sumTokMaster_inter_embT (f₁.rel_cod hrel)]⟩)
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inl ⟨X, X', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embF (f₀.rel_cod hrel)]
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inl ⟨X, X' ∩ X'₂, f₀.inter_right hrel hrel₂, rfl, embBit_inter false X' X'₂⟩)
      · exact absurd hWeq (embBit_ne (by decide) (A₀.ne X (f₀.rel_dom hrel)))
    · rcases h2 with ⟨-, rfl⟩ | ⟨X₂, X'₂, hrel₂, hWeq, rfl⟩ | ⟨Y₂, Y'₂, hrel₂, hWeq, rfl⟩
      · refine Or.inr (Or.inr ⟨Y, Y', hrel, rfl, ?_⟩)
        rw [Set.inter_comm, sumTokMaster_inter_embT (f₁.rel_cod hrel)]
      · exact absurd hWeq (embBit_ne (by decide) (A₁.ne Y (f₁.rel_dom hrel)))
      · obtain rfl := embBit_injective hWeq
        exact Or.inr (Or.inr ⟨Y, Y' ∩ Y'₂, f₁.inter_right hrel hrel₂, rfl, embBit_inter true Y' Y'₂⟩)
  mono := by
    rintro W W'' Z Z' h hWW hZZ' hW'' hZ'
    rcases h with ⟨-, rfl⟩ | ⟨X, X', hrel, rfl, rfl⟩ | ⟨Y, Y', hrel, rfl, rfl⟩
    · -- output was the master; a blunter neighbourhood must again be the master.
      exact Or.inl ⟨hW'', Set.Subset.antisymm ((B₀.sum B₁).sys.sub_master hZ') hZZ'⟩
    · -- input `0X`, output `0X'`. The sharper input `W''` and blunter output `Z'`.
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact Or.inr (Or.inl ⟨X₂, X₃,
            f₀.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hX₂ hX₃, rfl, rfl⟩)
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₁.ne Y₂ hY₂) hsub)
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₀.ne X' (f₀.rel_cod hrel)) hsub)
    · -- input `1Y`, output `1Y'`.
      rcases hZ' with rfl | ⟨X₃, hX₃, rfl⟩ | ⟨Y₃, hY₃, rfl⟩
      · exact Or.inl ⟨hW'', rfl⟩
      · exact absurd hZZ' (fun hsub =>
          embBit_not_subset_cross (by decide) (B₁.ne Y' (f₁.rel_cod hrel)) hsub)
      · rcases hW'' with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
        · exact absurd (hWW nil_mem_sumTokMaster) nil_not_mem_embBit
        · exact absurd hWW (fun hsub => embBit_not_subset_cross (by decide) (A₀.ne X₂ hX₂) hsub)
        · exact Or.inr (Or.inr ⟨Y₂, Y₃,
            f₁.mono hrel (embBit_subset.mp hWW) (embBit_subset.mp hZZ') hY₂ hY₃, rfl, rfl⟩)

/-! ## The functorial action of product on maps -/

/-- **`f₀ × f₁`, the action of the product functor on (approximable) maps.** A product
neighbourhood `{Λ} ∪ 0X ∪ 1Y` is sent to `{Λ} ∪ 0X' ∪ 1Y'` whenever `X f₀ X'` and `Y f₁ Y'`. -/
def prodMapTok (f₀ : ApproximableMap A₀.sys B₀.sys) (f₁ : ApproximableMap A₁.sys B₁.sys) :
    ApproximableMap (A₀.prod A₁).sys (B₀.prod B₁).sys where
  rel W W' := ∃ X Y X' Y', f₀.rel X X' ∧ f₁.rel Y Y' ∧
    W = prodTokNbhd X Y ∧ W' = prodTokNbhd X' Y'
  rel_dom := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, rfl, -⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_dom h0) (f₁.rel_dom h1)
  rel_cod := by
    rintro W W' ⟨X, Y, X', Y', h0, h1, -, rfl⟩
    exact prodTok_mem_prodTokNbhd (f₀.rel_cod h0) (f₁.rel_cod h1)
  master_rel :=
    ⟨A₀.sys.master, A₁.sys.master, B₀.sys.master, B₁.sys.master,
      f₀.master_rel, f₁.master_rel, rfl, rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ ⟨X₂, Y₂, X'₂, Y'₂, h0₂, h1₂, hWeq, rfl⟩
    obtain ⟨rfl, rfl⟩ := prodTokNbhd_injective hWeq
    exact ⟨X, Y, X' ∩ X'₂, Y' ∩ Y'₂, f₀.inter_right h0 h0₂, f₁.inter_right h1 h1₂, rfl,
      prodTokNbhd_inter X' X'₂ Y' Y'₂⟩
  mono := by
    rintro W W'' Z Z' ⟨X, Y, X', Y', h0, h1, rfl, rfl⟩ hWW hZZ' hW'' hZ'
    obtain ⟨X₂, Y₂, hX₂, hY₂, rfl⟩ := hW''
    obtain ⟨X'₃, Y'₃, hX'₃, hY'₃, rfl⟩ := hZ'
    obtain ⟨hsX, hsY⟩ := prodTokNbhd_subset_iff.mp hWW
    obtain ⟨hsX', hsY'⟩ := prodTokNbhd_subset_iff.mp hZZ'
    exact ⟨X₂, Y₂, X'₃, Y'₃, f₀.mono h0 hsX hsX' hX₂ hX'₃, f₁.mono h1 hsY hsY' hY₂ hY'₃, rfl, rfl⟩

/-! ## The bifunctor laws: identities and composition are preserved -/

/-! ## The functor-expression algebra `T(X)` and the functor laws

*"Generate all constructs `T(X)` formed by the constants (`T(X) = 𝒟`), by the identity (`T(X) = X`),
and by sums and products."* -/

/-- **The functor-expression algebra.** A `T(X)` built from constants, the identity, and binary sums
and products — Scott's closed family of constructs. -/
inductive FExpr where
  | const : ScottSys → FExpr
  | var : FExpr
  | sum : FExpr → FExpr → FExpr
  | prod : FExpr → FExpr → FExpr

/-- **The action of `T` on objects.** -/
def FExpr.obj : FExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum T₀ T₁, X => (T₀.obj X).sum (T₁.obj X)
  | .prod T₀ T₁, X => (T₀.obj X).prod (T₁.obj X)

/-- **The action of `T` on (approximable) maps.** Constants act by the identity, the identity functor
acts by `f` itself, and sums/products act by the bifunctorial combinators `sumMapTok`/`prodMapTok`. -/
def FExpr.map : (T : FExpr) → {X Y : ScottSys} → ApproximableMap X.sys Y.sys →
    ApproximableMap (T.obj X).sys (T.obj Y).sys
  | .const D, _, _, _ => idMap D.sys
  | .var, _, _, f => f
  | .sum T₀ T₁, _, _, f => sumMapTok (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f => prodMapTok (T₀.map f) (T₁.map f)

/-! ## Continuous on maps — the monotone half

Scott's *continuous on maps* (Definition 6.8) requires `λf. T(f)` to be approximable on the strict
function space; here we record its **monotonicity** (the order half of approximability — a sharper map
yields a sharper image), proved compositionally from the bifunctor combinators. -/

/-! ## Monotone on domains

Scott's *monotone on domains* (Definition 6.13): a subdomain relation `D ◁ E` is carried to
`T(D) ◁ T(E)`. Because every construct here stays over the single token type `{0,1}*`, the relation is
between systems on a common carrier (no transport needed), and the bifunctor combinators carry `◁`
componentwise. -/

/-! ## Continuous on domains

Scott's *continuous on domains* (Definition 6.13): `λD. T(D)` preserves directed unions of
subsystems. Concretely, if `U` is the union of a non-empty `◁`-directed family `ℱ` of subsystems of
`U`, then every neighbourhood of `T(U)` already appears in some `T(D)` with `D ∈ ℱ` (and conversely).
The forward direction is by induction; the products use directedness to merge the two component
witnesses into a single `D`. -/

/-! ## Continuous on maps — full directed-sup preservation

Scott's *continuous on maps* (Definition 6.8): `λf. T(f)` is approximable, equivalently (Exercise
2.13) it is continuous — monotone (`map_mono`) and preserving directed unions of maps. If `f` is the
pointwise union of a non-empty directed family `gᵢ`, then `T(f)` is the pointwise union of the
`T(gᵢ)`. The products use directedness to merge the two component witnesses. -/

/-! ## Exercise 6.20 — `λΓ. tok(T({Γ}))` is continuous, hence a fixed point exists

> For any system `𝒟` let `tok(𝒟)` be the underlying set of tokens, so that `𝒟` is a system over
> `tok(𝒟)`. For the category of Exercise 6.19 show that the function `λΓ. tok(T({Γ}))` is continuous
> on the domain `{Γ ⊆ {0,1}* ∣ Λ ∈ Γ}`, where `T` is any of the functors generated in 6.19. Conclude
> that there must exist a set `Γ = tok(T({Γ}))`, so that `{Γ} ◁ T({Γ})`, and so 6.14 applies.

Here `tok(𝒟) = 𝒟.master` (the master neighbourhood *is* the token set `Δ`, since `𝒟 ⊆ 𝒫(Δ)`), and
`{Γ}` is the one-neighbourhood system `singletonSys Γ` with master `Γ`. The key simplification is
that the *master* of `T({Γ})` is computed by a tiny token-level recursion `mFun T` that needs no
`NeighborhoodSystem` data at all: constants are constant, the identity returns `Γ`, and **both** sum
and product return `{Λ} ∪ 0·(…) ∪ 1·(…)` (`sumTokMaster = prodTokNbhd` on masters). `mFun_eq_master`
identifies `mFun T Γ` with `tok(T({Γ}))`. The function `mFun T` is monotone (`mFun_mono`) and
continuous — in fact fully additive — on the powerset of `{0,1}*` (`mFun_continuous`), so its
restriction to `{Γ ∣ Λ ∈ Γ}` is continuous on that domain. The least fixed point above the bottom
`{Λ}` is the explicit Kleene union `⋃ₙ mFunⁿ({Λ})` (`mIter`), giving `Γ = tok(T({Γ}))`
(`exists_tok_fixedPoint`) and hence `{Γ} ◁ T({Γ})` (`exists_singleton_subsystem`), exactly the
hypothesis Theorem 6.14 needs. (For the bottom to stay in the domain we need `Λ ∈ tok(C)` for the
constant systems `C`; this is recorded by `FExpr.RootedConst`, and holds automatically for sums and
products since their masters contain `Λ`.) -/

/-- **`tok(𝒟)`** — the underlying set of tokens of a system, i.e. its master neighbourhood `Δ`. -/
def ScottSys.tok (D : ScottSys) : Set Str := D.sys.master

/-- **The one-neighbourhood system `{Γ}`** over `{0,1}*`: its only neighbourhood is `Γ` itself, and
its master (token set) is `Γ`. It is `∅`-free precisely because `Γ` is non-empty. -/
def singletonSys (Γ : Set Str) (h : Γ.Nonempty) : ScottSys where
  sys :=
    { mem := fun X => X = Γ
      master := Γ
      master_nonempty := h
      master_mem := rfl
      inter_mem := by
        intro X Y Z hX hY _ _
        show X ∩ Y = Γ
        rw [hX, hY, Set.inter_self]
      sub_master := by intro X hX; rw [show X = Γ from hX] }
  ne := by intro X hX; rw [show X = Γ from hX]; exact h

/-- **The token-level master recursion.** `mFun T Γ` computes `tok(T({Γ}))` purely from `Γ`, without
touching the neighbourhood data of `{Γ}` (`mFun_eq_master`): constants are constant, the identity
returns `Γ`, and both sum and product wrap the two component token sets with the tags `0,1` under a
common root `Λ` (`sumTokMaster = prodTokNbhd` agree on masters). -/
def mFun : FExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
  | .prod T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))

/-- `mFun T Γ` is exactly the token set `tok(T({Γ})) = (T.obj {Γ}).sys.master`. -/
theorem mFun_eq_master : (T : FExpr) → {Γ : Set Str} → (h : Γ.Nonempty) →
    mFun T Γ = (T.obj (singletonSys Γ h)).sys.master
  | .const _, _, _ => rfl
  | .var, _, _ => rfl
  | .sum T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]
  | .prod T₀ T₁, Γ, h => by
      show insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
        = insert ([] : Str) (embBit false ((T₀.obj (singletonSys Γ h)).sys.master)
            ∪ embBit true ((T₁.obj (singletonSys Γ h)).sys.master))
      rw [mFun_eq_master T₀ h, mFun_eq_master T₁ h]

/-! ### Monotone on the domain -/

/-- Monotonicity of the tagged-union shape shared by sum and product. -/
theorem insertTag_mono {p q p' q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') :
    insert ([] : Str) (embBit false p ∪ embBit true q)
      ⊆ insert ([] : Str) (embBit false p' ∪ embBit true q') := by
  rintro w (rfl | hw | hw)
  · exact Or.inl rfl
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

/-- **`λΓ. tok(T({Γ}))` is monotone on the domain.** -/
theorem mFun_mono (T : FExpr) {Γ Γ' : Set Str} (h : Γ ⊆ Γ') : mFun T Γ ⊆ mFun T Γ' := by
  induction T with
  | const C => exact subset_rfl
  | var => exact h
  | sum T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁
  | prod T₀ T₁ ih₀ ih₁ => exact insertTag_mono ih₀ ih₁

/-! ### Continuous on the domain -/

/-- Continuity (full additivity) of the tagged-union shape shared by sum and product. -/
theorem insertTag_continuous {ℱ : Set (Set Str)} {U : Set Str} (hne : ℱ.Nonempty)
    {p q : Set Str → Set Str}
    (hp : ∀ w, w ∈ p U ↔ ∃ Γ ∈ ℱ, w ∈ p Γ)
    (hq : ∀ w, w ∈ q U ↔ ∃ Γ ∈ ℱ, w ∈ q Γ) (w : Str) :
    (w ∈ insert ([] : Str) (embBit false (p U) ∪ embBit true (q U)))
      ↔ ∃ Γ ∈ ℱ, w ∈ insert ([] : Str) (embBit false (p Γ) ∪ embBit true (q Γ)) := by
  simp only [Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro (rfl | hw | hw)
    · obtain ⟨Γ, hΓ⟩ := hne; exact ⟨Γ, hΓ, Or.inl rfl⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hpΓ⟩ := (hp w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inl ⟨w', rfl, hpΓ⟩)⟩
    · obtain ⟨w', rfl, hw'⟩ := hw
      obtain ⟨Γ, hΓ, hqΓ⟩ := (hq w').mp hw'
      exact ⟨Γ, hΓ, Or.inr (Or.inr ⟨w', rfl, hqΓ⟩)⟩
  · rintro ⟨Γ, hΓ, (rfl | hw | hw)⟩
    · exact Or.inl rfl
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inl ⟨w', rfl, (hp w').mpr ⟨Γ, hΓ, hw'⟩⟩)
    · obtain ⟨w', rfl, hw'⟩ := hw
      exact Or.inr (Or.inr ⟨w', rfl, (hq w').mpr ⟨Γ, hΓ, hw'⟩⟩)

/-- **`λΓ. tok(T({Γ}))` is continuous on the domain `{Γ ∣ Λ ∈ Γ}`.** For a non-empty `⊆`-directed
family `ℱ` with union `U`, the token set of `T({U})` is the union of those of the `T({Γ})`. (The
proof in fact establishes full additivity — directedness is not needed for the master level — but the
statement is the directed-sup form Scott calls *continuous*.) -/
theorem mFun_continuous (T : FExpr) {ℱ : Set (Set Str)} {U : Set Str}
    (_hdir : DirectedOn (· ⊆ ·) ℱ) (hne : ℱ.Nonempty)
    (hU : ∀ w, w ∈ U ↔ ∃ Γ ∈ ℱ, w ∈ Γ) :
    ∀ w, w ∈ mFun T U ↔ ∃ Γ ∈ ℱ, w ∈ mFun T Γ := by
  induction T with
  | const C =>
      intro w
      exact ⟨fun hw => let ⟨Γ, hΓ⟩ := hne; ⟨Γ, hΓ, hw⟩, fun ⟨_, _, hw⟩ => hw⟩
  | var => intro w; exact hU w
  | sum T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w
  | prod T₀ T₁ ih₀ ih₁ => intro w; exact insertTag_continuous hne ih₀ ih₁ w

/-! ### A fixed point `Γ = tok(T({Γ}))` — so `{Γ} ◁ T({Γ})` and 6.14 applies -/

/-- **`Λ ∈ tok(C)` for every constant `C` occurring in `T`.** This is what keeps the bottom `{Λ}` and
the whole Kleene chain inside the domain `{Γ ∣ Λ ∈ Γ}`; sums and products satisfy it for free. -/
def FExpr.RootedConst : FExpr → Prop
  | .const C => ([] : Str) ∈ C.sys.master
  | .var => True
  | .sum a b => a.RootedConst ∧ b.RootedConst
  | .prod a b => a.RootedConst ∧ b.RootedConst

/-- If `Λ ∈ Γ` then `Λ ∈ tok(T({Γ}))` — so `λΓ. tok(T({Γ}))` is an endofunction of the domain. -/
theorem mFun_nil_mem : ∀ (T : FExpr), T.RootedConst → {Γ : Set Str} →
    ([] : Str) ∈ Γ → ([] : Str) ∈ mFun T Γ
  | .const _, hC, _, _ => hC
  | .var, _, _, hΓ => hΓ
  | .sum _ _, _, _, _ => Set.mem_insert _ _
  | .prod _ _, _, _, _ => Set.mem_insert _ _

/-- The **Kleene iteration** `mFunⁿ({Λ})` whose union is the least fixed point above `{Λ}`. -/
def mIter (T : FExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => mFun T (mIter T n)

theorem nil_mem_mIter (T : FExpr) (hT : T.RootedConst) : ∀ n, ([] : Str) ∈ mIter T n
  | 0 => rfl
  | n + 1 => mFun_nil_mem T hT (nil_mem_mIter T hT n)

theorem mIter_mono_step (T : FExpr) (hT : T.RootedConst) :
    ∀ n, mIter T n ⊆ mIter T (n + 1)
  | 0 => by
      intro w hw
      have hw' : w = [] := hw
      subst hw'
      exact mFun_nil_mem T hT rfl
  | n + 1 => mFun_mono T (mIter_mono_step T hT n)

theorem mIter_mono (T : FExpr) (hT : T.RootedConst) {m n : ℕ} (hmn : m ≤ n) :
    mIter T m ⊆ mIter T n := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => intro x hx; exact mIter_mono_step T hT _ (ih hx)

/-- The Kleene union is a **fixed point** of `λΓ. tok(T({Γ}))`. -/
theorem mFun_iter_fixed (T : FExpr) (hT : T.RootedConst) :
    mFun T (⋃ n, mIter T n) = ⋃ n, mIter T n := by
  have hstep := mIter_mono_step T hT
  have hne : (Set.range (mIter T)).Nonempty := ⟨mIter T 0, 0, rfl⟩
  have hdir : DirectedOn (· ⊆ ·) (Set.range (mIter T)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ⟨mIter T (max i j), ⟨max i j, rfl⟩,
      mIter_mono T hT (le_max_left i j), mIter_mono T hT (le_max_right i j)⟩
  have hU : ∀ v, v ∈ (⋃ n, mIter T n) ↔ ∃ S ∈ Set.range (mIter T), v ∈ S := by
    intro v
    constructor
    · intro hv; rw [Set.mem_iUnion] at hv; obtain ⟨n, hn⟩ := hv
      exact ⟨mIter T n, ⟨n, rfl⟩, hn⟩
    · rintro ⟨S, ⟨n, rfl⟩, hv⟩; exact Set.mem_iUnion.mpr ⟨n, hv⟩
  apply Set.ext; intro w
  rw [mFun_continuous T hdir hne hU w]
  constructor
  · rintro ⟨S, ⟨n, rfl⟩, hwS⟩; exact Set.mem_iUnion.mpr ⟨n + 1, hwS⟩
  · intro hw
    rw [Set.mem_iUnion] at hw; obtain ⟨n, hn⟩ := hw
    exact ⟨mIter T n, ⟨n, rfl⟩, hstep n hn⟩

/-- **The conclusion of Exercise 6.20 (token level).** For any construct `T` whose constants contain
`Λ`, there is a set `Γ` with `Λ ∈ Γ` and `Γ = tok(T({Γ}))`. -/
theorem exists_tok_fixedPoint (T : FExpr) (hT : T.RootedConst) :
    ∃ Γ : Set Str, ([] : Str) ∈ Γ ∧ mFun T Γ = Γ :=
  ⟨⋃ n, mIter T n, Set.mem_iUnion.mpr ⟨0, nil_mem_mIter T hT 0⟩, mFun_iter_fixed T hT⟩

/-- **The conclusion of Exercise 6.20 (object level): `{Γ} ◁ T({Γ})`, so Theorem 6.14 applies.**
From the fixed point `Γ = tok(T({Γ}))`, the one-neighbourhood system `{Γ}` is a subsystem of
`T({Γ})`: they share the master `Γ`, and `Γ` is a (the master) neighbourhood of `T({Γ})`. -/
theorem exists_singleton_subsystem (T : FExpr) (hT : T.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ, hnil, hfix⟩ := exists_tok_fixedPoint T hT
  have hne : Γ.Nonempty := ⟨[], hnil⟩
  -- `tok(T({Γ})) = Γ` (note `tok` is definitionally `.sys.master`).
  have hmaster : (T.obj (singletonSys Γ hne)).sys.master = Γ :=
    (mFun_eq_master T hne).symm.trans hfix
  refine ⟨Γ, hne, ?_, ?_, ?_⟩
  · -- master_eq: `Γ = tok(T({Γ}))`
    exact hmaster.symm
  · -- sub: the only neighbourhood `Γ` of `{Γ}` is the master of `T({Γ})`
    intro X hX
    have heq : X = (T.obj (singletonSys Γ hne)).sys.master := (hX : X = Γ).trans hmaster.symm
    rw [heq]
    exact (T.obj (singletonSys Γ hne)).sys.master_mem
  · -- inter_closed: trivial, both neighbourhoods are `Γ`
    intro X Y hX hY _
    show X ∩ Y = Γ
    rw [show X = Γ from hX, show Y = Γ from hY, Set.inter_self]
end Exercise619
end DomainTheory.Neighborhood
