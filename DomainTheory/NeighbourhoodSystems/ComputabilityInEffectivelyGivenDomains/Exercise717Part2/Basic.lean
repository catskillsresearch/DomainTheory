/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel

@[expose] public section

/-!
# Exercise 7.17 (Scott 1981, PRG-19, §7) — Part 2: the universal strict mapping `g : D^§ → E`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.17.** … Prove also that if `E` is effectively given and `u : D → E` and
> `v : E × E → E` are computable, then the unique strict mapping `g : D^§ → E`, where
> `g(in x) = u(x)` and `g(pair(y, z)) = v(g(y), g(z))`, is a computable mapping.

This is the *catamorphism* (fold) out of the tree algebra `D^§ ≅ D + (D^§ × D^§)` (Example 6.1) into a
`T`-algebra structure `(E, [u, v])`. We build `g` directly as a neighbourhood relation `GRel u v`,
defined by recursion on the three `D^§`-neighbourhood shapes:

* `Γ            ↦ Δ_E`              (strict: `⊥ ↦ ⊥`);
* `0·X          ↦ u`'s relation on `X`;
* `1·P ∪ 2·Q    ↦ ∃ Z₁ Z₂, P g Z₁ ∧ Q g Z₂ ∧ ⟨Z₁,Z₂⟩ v Z`.

There is **no separate "top" clause**: because `u` and `v` are approximable (they relate `Δ ↦ Δ`),
`GRel u v W Δ_E` already holds for every `W ∈ 𝒟^§` (`gRel_master`). The three clauses give an
honest `ApproximableMap` (`gMap`), with the two defining equations
`gMap_in : g(in x) = u(x)` and `gMap_pair : g(pair y z) = v(⟨g y, g z⟩)`, and strictness
`gMap_strict`.

The **computability** (`gMap_isComputable`) is the heart of the exercise. The index relation
`R m k := GRel u v (V_m)(Y_k)` (`V` = `Vsharp` the `D^§` enumeration, `Y` = `Q`'s enumeration of `E`)
satisfies the recursive characterisation `gRel_index_*`. We realise it as the recursively-enumerable
existential `∃ cert` over a **stack-machine certificate**: a derivation is a postorder *program* of
push/pop instructions verified by a single primitive-recursive `foldCode`, exactly the device used for
`fix` in Theorem 7.6. (A per-`Vsharp`-index memo — as in `dsharpStep` — does **not** work here, since
`R` is a genuine relation: the same sub-neighbourhood may be folded to *different* outputs in different
parts of the tree, so the certificate must mirror the derivation tree.)

Data and the two equations are choice-free `⊆ {propext, Quot.sound}`; the `IsComputableMap` proof and
the inversion lemmas route through `Classical` (`Set` reasoning over the arbitrary carriers `α`, `β`),
as everywhere in this layer.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

/-! ### The catamorphism relation `GRel u v`. -/

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Related inputs are `D^§`-neighbourhoods. -/
theorem gRel_dom {W Z} (h : GRel u v W Z) : MemS D W := by
  induction h with
  | gamma _ => exact MemS.gamma
  | leaf hrel => exact MemS.zero (u.rel_dom hrel)
  | node _ _ _ ihP ihQ => exact MemS.pair ihP ihQ

/-- Related outputs are `E`-neighbourhoods. -/
theorem gRel_cod {W Z} (h : GRel u v W Z) : E.mem Z := by
  induction h with
  | gamma hZ => exact hZ ▸ E.master_mem
  | leaf hrel => exact u.rel_cod hrel
  | node _ _ hvrel _ _ => exact v.rel_cod hvrel

/-- **Strictness in the relation: every `D^§`-neighbourhood folds to `Δ_E`.** This is why no separate
"top" clause is needed — `u`/`v` relate `Δ ↦ Δ`, so the master propagates through the tree. -/
theorem gRel_master : ∀ {W}, MemS D W → GRel u v W E.master := by
  intro W hW
  induction hW with
  | gamma => exact GRel.gamma rfl
  | @zero X hX =>
      exact GRel.leaf ((u.rel_iff_mem_principal hX).mpr (u.toElementMap _).master_mem)
  | @pair P Q _ _ ihP ihQ =>
      refine GRel.node ihP ihQ ?_
      have h := v.master_rel
      rwa [prod_master] at h

/-! ### Shape inversion lemmas. -/

/-- `embZero X ≠ embPair P Q` from `P ∈ 𝒟^§` (no `D.mem X` needed). -/
theorem embZero_ne_embPair_of_memS (hD : ∀ X, D.mem X → X.Nonempty)
    {X : Set α} {P Q : Set (List Bool × α)} (hP : MemS D P) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨z, hz⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
  have hz0 : z ∈ embZero X := h ▸ hz
  have hpath : z.1 = [] := hz0.1
  rcases hz with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · rw [hp'] at hpath; simp at hpath
  · rw [hq'] at hpath; simp at hpath

/-- Inversion at `Γ`: `Γ g Z` forces `Z = Δ_E` (Scott's strictness). -/
theorem gRel_gamma_inv (hD : ∀ X, D.mem X → X.Nonempty) {Z}
    (h : GRel u v (Gamma D) Z) : Z = E.master := by
  generalize hW : Gamma D = W at h
  cases h with
  | gamma hZ => exact hZ
  | @leaf X Z hrel => exact absurd hW.symm (embZero_ne_Gamma D hD X)
  | @node P Q Z₁ Z₂ Z hP hQ hvrel => exact absurd hW.symm (embPair_ne_Gamma D hD P Q)

/-- Inversion at a leaf `0·X`: `0·X g Z ↔ X u Z`. -/
theorem gRel_embZero_inv (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α} {Z}
    (h : GRel u v (embZero X) Z) : u.rel X Z := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma hZ => exact absurd hW (embZero_ne_Gamma D hD X)
  | @leaf X' Z' hrel => rw [embZero_injective hW]; exact hrel
  | @node P Q Z₁ Z₂ Z hP hQ hvrel =>
      exact absurd hW (embZero_ne_embPair_of_memS hD (gRel_dom hP))

/-- Inversion at a node `1·P ∪ 2·Q`: `(1·P∪2·Q) g Z ↔ ∃ Z₁ Z₂, P g Z₁ ∧ Q g Z₂ ∧ ⟨Z₁,Z₂⟩ v Z`. -/
theorem gRel_embPair_inv (hD : ∀ X, D.mem X → X.Nonempty) {P Q : Set (List Bool × α)} {Z}
    (h : GRel u v (embPair P Q) Z) :
    ∃ Z₁ Z₂, GRel u v P Z₁ ∧ GRel u v Q Z₂ ∧ v.rel (prodNbhd Z₁ Z₂) Z := by
  have hPQ := gRel_dom h
  obtain ⟨hPmem, hQmem⟩ := memS_embPair_inv hD hPQ
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma hZ => exact absurd hW (embPair_ne_Gamma D hD P Q)
  | @leaf X Z hrel => exact absurd hW.symm (embZero_ne_embPair_of_memS hD hPmem)
  | @node P' Q' Z₁ Z₂ Z hP' hQ' hvrel =>
      obtain ⟨rfl, rfl⟩ := embPair_injective hW
      exact ⟨Z₁, Z₂, hP', hQ', hvrel⟩

/-! ### The `ApproximableMap` laws. -/

/-- Monotonicity (Scott's 2.1(iii)). -/
theorem gRel_mono (hD : ∀ X, D.mem X → X.Nonempty) {W Z} (h : GRel u v W Z) :
    ∀ {W' Z'}, W' ⊆ W → Z ⊆ Z' → MemS D W' → E.mem Z' → GRel u v W' Z' := by
  induction h with
  | @gamma Z hZ =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      subst hZ
      have hZ' : Z' = E.master := Set.Subset.antisymm (E.sub_master hZ'mem) hZZ'
      subst hZ'
      exact gRel_master hW'mem
  | @leaf X Z hrel =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      obtain ⟨X', hX'mem, rfl⟩ := memS_sub_embZero hD hW'mem hW'W
      exact GRel.leaf (u.mono hrel (embZero_subset.mp hW'W) hZZ' hX'mem hZ'mem)
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      obtain ⟨P', Q', hP'mem, hQ'mem, rfl⟩ := memS_sub_embPair hD hW'mem hW'W
      obtain ⟨hP'P, hQ'Q⟩ := embPair_subset.mp hW'W
      refine GRel.node (ihP hP'P subset_rfl hP'mem (gRel_cod hP))
        (ihQ hQ'Q subset_rfl hQ'mem (gRel_cod hQ)) ?_
      exact v.mono hvrel subset_rfl hZZ'
        (prod_mem_prodNbhd (gRel_cod hP) (gRel_cod hQ)) hZ'mem

/-- Intersectivity on the output (Scott's 2.1(ii)). -/
theorem gRel_interRight (hD : ∀ X, D.mem X → X.Nonempty) {W Z} (h : GRel u v W Z) :
    ∀ {Z'}, GRel u v W Z' → GRel u v W (Z ∩ Z') := by
  induction h with
  | @gamma Z hZ =>
      intro Z' h'
      subst hZ
      have hZ' := gRel_gamma_inv hD h'
      subst hZ'
      rw [Set.inter_self]
      exact GRel.gamma rfl
  | @leaf X Z hrel =>
      intro Z' h'
      exact GRel.leaf (u.inter_right hrel (gRel_embZero_inv hD h'))
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      intro Z' h'
      obtain ⟨Z₁', Z₂', hP', hQ', hv'⟩ := gRel_embPair_inv hD h'
      have hgP : GRel u v P (Z₁ ∩ Z₁') := ihP hP'
      have hgQ : GRel u v Q (Z₂ ∩ Z₂') := ihQ hQ'
      refine GRel.node hgP hgQ ?_
      have hmem : (prod E E).mem (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) :=
        prod_mem_prodNbhd (gRel_cod hgP) (gRel_cod hgQ)
      have hv1 : v.rel (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) Z :=
        v.mono hvrel (prodNbhd_subset_iff.mpr ⟨Set.inter_subset_left, Set.inter_subset_left⟩)
          subset_rfl hmem (v.rel_cod hvrel)
      have hv2 : v.rel (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) Z' :=
        v.mono hv' (prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩)
          subset_rfl hmem (v.rel_cod hv')
      exact v.inter_right hv1 hv2

/-- **Exercise 7.17 Part 2 — the universal strict map `g : D^§ → E`.** -/
def gMap (u : ApproximableMap D E) (v : ApproximableMap (prod E E) E)
    (hD : ∀ X, D.mem X → X.Nonempty) : ApproximableMap (Dsharp D hD) E where
  rel := GRel u v
  rel_dom h := gRel_dom h
  rel_cod h := gRel_cod h
  master_rel := GRel.gamma rfl
  inter_right h h' := gRel_interRight hD h h'
  mono h hsub hsup hX' hY' := gRel_mono hD h hsub hsup hX' hY'

@[simp] theorem gMap_rel {hD : ∀ X, D.mem X → X.Nonempty} {W : Set (List Bool × α)} {Z : Set β} :
    (gMap u v hD).rel W Z ↔ GRel u v W Z := Iff.rfl

/-! ### The two defining equations and strictness. -/

/-! ### `Nat.pair` monotonicity (for the certificate measure).

The certificate is read by the `Proposition77` course-of-values memo (`gOf`/`rtbl`/`listGet`) over the
combined code `w = ⟨v, cert⟩`. A node's child code `⟨a.i, child-cert⟩` must be strictly `< w`. The
`Vsharp`-index strictly decreases (`a.i < v`) while the child-cert is only `≤ cert`, so we need
`Nat.pair` strictly monotone in its first argument (second fixed) and monotone in its second. -/

/-! ### The stack-machine / course-of-values certificate evaluator.

`R n m := GRel u v (V_n)(Q_m)` (`V` = `Vsharp`, `Q` = `Q.X`) satisfies the recursion: `n = 0`
folds to `Δ_E`; `n = 2a+1` folds via `u`; `n = 2a+2` is `∃ Z₁ Z₂, V_{a.1} g Z₁ ∧ V_{a.2} g Z₂ ∧
⟨Z₁,Z₂⟩ v Q_m`. A *derivation* is a finite tree (the same `V` may fold to *different* outputs in
different positions, so the witness must mirror the tree). We encode it as a single `cert` and verify
it with the `Proposition77` memo `gOf`/`rtbl` over `w = ⟨v, cert⟩`: at each node the two children's
results (`okBit`, `outIdx`) are read from the memo table by `listGet`. The step is fed the four
primitive-recursive `{0,1}`/index functions `fe` (`Q`-equality-to-`Δ`), `fU`/`fV` (the deciders of
`u`/`v`'s r.e. relations), and `mIdx` (`Q`'s master index). -/

section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)

/-- **The certificate step.** Input `p = ⟨w, tbl⟩` with `w = ⟨n, cert⟩` and `tbl` the memo table.
`cert` decodes to `⟨out, wit, lcert, rcert⟩`. Returns `⟨okBit, out⟩`:
* `n = 0`   : `okBit = fe⟨out, mIdx⟩` (is `Q_out = Δ_E`?);
* `n = 2a+1`: `okBit = fU⟨wit, ⟨a, out⟩⟩` (does `wit` witness `X_a u Q_out`?);
* `n = 2a+2`: read children `⟨a.1, lcert⟩`, `⟨a.2, rcert⟩` from `tbl`; `okBit = okL·okR·
  fV⟨wit, ⟨⟨outL, outR⟩, out⟩⟩`. -/
def gStep (p : ℕ) : ℕ :=
  let w := p.unpair.1
  let tbl := p.unpair.2
  let nn := w.unpair.1
  let cert := w.unpair.2
  let out := cert.unpair.1
  let wit := cert.unpair.2.unpair.1
  let lcert := cert.unpair.2.unpair.2.unpair.1
  let rcert := cert.unpair.2.unpair.2.unpair.2
  let b := nn / 2 - 1
  let childL := listGet tbl (w - 1 - Nat.pair b.unpair.1 lcert)
  let childR := listGet tbl (w - 1 - Nat.pair b.unpair.2 rcert)
  selectFn (1 - nn)
    (Nat.pair (fe (Nat.pair out mIdx)) out)
    (selectFn (nn % 2)
      (Nat.pair (fU (Nat.pair wit (Nat.pair (nn / 2) out))) out)
      (Nat.pair (childL.unpair.1 * childR.unpair.1
          * fV (Nat.pair wit (Nat.pair (Nat.pair childL.unpair.2 childR.unpair.2) out))) out))

/-- The full evaluator: the course-of-values value of `gStep` at `w = ⟨n, cert⟩`. -/
def gEval : ℕ → ℕ := gOf (gStep fe fU fV mIdx)

end Computability

/-! ### Computability of `g`. -/
end Exercise717
end DomainTheory.NeighbourhoodSystems
