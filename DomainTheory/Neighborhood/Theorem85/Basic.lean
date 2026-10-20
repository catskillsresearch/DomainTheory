/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.ApproximableExercises

/-!
# Lecture VIII — Theorem 8.5 (Scott 1981, PRG-19): finitary projections via a step-closure formula

**Theorem 8.5.** For an approximable mapping `a : E → E` the following are equivalent:

(i) `a` is a finitary projection;

(ii) `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ X a X}`, for all `x ∈ |E|`.

## What is formalized here

The **`(ii) ⟹ (i)` direction** (`isFinitaryProjection_of_formula`) is proved in full, and is what
Theorem 8.6 actually needs: `sub`'s fixed points are *by definition* exactly the maps `a`
satisfying formula (ii), so characterising the range of `sub` only ever needs this direction.

The construction: from `a`, build `D := {X ∈ E ∣ X a X}` directly (`fixedNbhd`) — this is a genuine
subsystem `D ◁ E` **for any approximable map `a`** (`fixedNbhd_subsystem`), no hypothesis on `a`
needed for the neighbourhood-system axioms themselves. Formula (ii), unwound at principal elements
via `rel_iff_mem_principal`, says exactly that `a`'s relation matches Proposition 8.2's formula for
`D`: `a = retractionOfSubsystem (fixedNbhd_subsystem a)`. Proposition 8.2 (via Definition 8.3's
corollaries) then hands us `IsFinitaryProjection a` for free.

**The `(i) ⟹ (ii)` direction is *not* formalized in this file.** Scott's own proof needs a fact not
yet in the codebase: a section/retraction pair `i ⊣ j` (`j∘i = I_D`) built from the abstract
"isomorphic to a domain" witness of `IsFinitary` *reflects compactness* — if `i(w)` is a principal
(finite) element of `E` then `w` is already principal in `D`. (Scott's own remark: "`i(j(↑X)) = ↑X`
means `j(↑X)` is a finite element of `D`".) This is provable from existing machinery (`iSupDirected`/
`toElementMap_iSupDirected` give continuity of `i`, and `D`'s general algebraicity gives that every
element is a directed union of its principal approximants — a compact element equalling a directed
sup must already equal one of the sup's members), but assembling it is a standalone, comparably
sized effort to the rest of this file and is left as a documented follow-up; see `HANDOFF.md`.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The candidate subdomain of Theorem 8.5's proof, `D = {X ∈ E ∣ X a X}`.** Built for *any*
approximable map `a : E → E` — the neighbourhood-system axioms need only `mono`/`inter_right` of
`a`, no projection or finitary hypothesis. (This is also exactly Theorem 8.6's `Fix(sub)` predicate
`X sub(f) X`, restated for a single map `a` in place of the function-space token `f`.) -/
def fixedNbhd (a : ApproximableMap E E) : NeighborhoodSystem α where
  mem X := E.mem X ∧ a.rel X X
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨E.master_mem, a.master_rel⟩
  inter_mem := by
    rintro X Y Z ⟨hXE, hXa⟩ ⟨hYE, hYa⟩ ⟨hZE, _⟩ hZsub
    have hXYE : E.mem (X ∩ Y) := E.inter_mem hXE hYE hZE hZsub
    have h1 : a.rel (X ∩ Y) X :=
      a.mono hXa Set.inter_subset_left subset_rfl hXYE hXE
    have h2 : a.rel (X ∩ Y) Y :=
      a.mono hYa Set.inter_subset_right subset_rfl hXYE hYE
    exact ⟨hXYE, a.inter_right h1 h2⟩
  sub_master := fun h => E.sub_master h.1

@[simp] theorem fixedNbhd_mem {a : ApproximableMap E E} {X : Set α} :
    (fixedNbhd a).mem X ↔ E.mem X ∧ a.rel X X := Iff.rfl

/-! ## Algebraicity and compactness

General-purpose lemmas about any `NeighborhoodSystem`, needed for Theorem 8.5's hard direction
below: every element is the directed union of its own principal ("finite"/compact) approximants
(`eq_iSupDirected_principal`), and this makes "compact" (in the standard directed-sup sense)
exactly synonymous with "principal" (`IsCompactElt`, `IsCompactElt.eq_principal`). -/

section Algebraic

variable {γ : Type u} {V : NeighborhoodSystem γ}

instance instNonemptyMemSubtype (x : V.Element) : Nonempty {X : Set γ // x.mem X} :=
  ⟨⟨V.master, x.master_mem⟩⟩

/-- A neighbourhood `Z` witnessing `y`'s membership is always a *lower bound* on `y`: `↑Z ⊑ y`.
The general form of `Basic.lean`'s remark that `⊥ = ↑Δ` is least: any witnessed `↑Z` sits below
the element it witnesses. -/
theorem principal_le_of_mem {y : V.Element} {Z : Set γ} (hZ : y.mem Z) :
    V.principal (y.sub hZ) ≤ y :=
  fun _ ⟨hW, hZW⟩ => y.up_mem hZ hW hZW

theorem principalFamily_directed (x : V.Element) :
    ∀ i j : {X : Set γ // x.mem X}, ∃ k : {X : Set γ // x.mem X},
      V.principal (x.sub i.2) ≤ V.principal (x.sub k.2) ∧
        V.principal (x.sub j.2) ≤ V.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

/-- **Algebraicity.** Every element `x` is the directed union of its own principal
("finite"/compact) approximants: `x = ⋃ {↑X ∣ X ∈ x}`, now literally as an `iSupDirected`
(rather than `eq_iUnion_principal`'s membership-only form). -/
theorem eq_iSupDirected_principal (x : V.Element) :
    x = iSupDirected (fun i : {X : Set γ // x.mem X} => V.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

/-- **Compactness, as a standalone predicate**: `x` is compact iff every time `x` sits below a
directed union it already sits below one of the summands. By algebraicity, this is exactly the
same thing as being principal (`eq_principal_of_isCompactElt`). Stated with `I` fixed to `V`'s own
token universe (the only instantiation ever needed below), to sidestep spurious universe-metavariable
friction from a separately-auto-bound `Type*` inside a reusable `def`. -/
def IsCompactElt (x : V.Element) : Prop :=
  ∀ {I : Type u} [Nonempty I] (d : I → V.Element) (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k),
    x ≤ iSupDirected d hdir → ∃ i, x ≤ d i

end Algebraic

/-! ## Theorem 8.5, `(i) ⟹ (ii)`: the hard direction

Setup: `a : E → E` is a retraction (`IsRetraction a`) and a projection (`a ≤ idMap E`), and its
fixed-point set is order-isomorphic to `F.Element` for some neighbourhood system `F` (`IsFinitary
a`, witnessed by `e`). We build the "section" `i : F → E` induced by `e` directly via `ofMono`
(Exercise 2.8), show it realizes `e.symm` at *every* element of `F` (not just principal ones,
`toElementMap_sectionMap`), and combine this with the algebraicity/compactness lemmas above to
prove Scott's compactness-reflection fact and, from it, formula (ii). -/

section HardDirection

variable {a : ApproximableMap E E}

/-- The sup of a directed family of `a`-fixed elements is again `a`-fixed: `a` is continuous
(`toElementMap_iSupDirected`), so `a` applied to the sup is the sup of `a` applied pointwise, which
is the original family by `hfix`. -/
theorem toElementMap_iSupDirected_fixed {I : Type u} [Nonempty I] (d : I → E.Element)
    (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k) (hfix : ∀ i, a.toElementMap (d i) = d i) :
    a.toElementMap (iSupDirected d hdir) = iSupDirected d hdir := by
  rw [toElementMap_iSupDirected]
  apply Element.ext
  intro Z
  rw [mem_iSupDirected, mem_iSupDirected]
  simp_rw [hfix]

/-- The fixed-point set of `a`, as a bare type — matching `IsFinitary`'s witness type. -/
abbrev FixSet (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}

variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)

/-- **The section `i : F → E`** induced by the abstract witness `e` of `IsFinitary a`: on the
principal element `↑X` of `F`, `i` returns the underlying `E`-element of `e.symm(↑X) ∈ Fix(a)`.
Built via `ofMono` (Exercise 2.8) — monotone on principals is all that's needed. -/
def sectionMap : ApproximableMap F E :=
  ofMono (fun _X hX => (e.symm (F.principal hX)).1) (fun _ _ hX hX' hXX' =>
    e.symm.monotone ((F.principal_le_iff hX hX').mpr hXX'))

@[simp] theorem toElementMap_sectionMap_principal {X : Set β} (hX : F.mem X) :
    (sectionMap e).toElementMap (F.principal hX) = (e.symm (F.principal hX)).1 :=
  toElementMap_ofMono_principal _ _ X hX

/-- **Claim′.** `i` realizes `e.symm` at *every* element of `F`, not just the principal ones:
`i(w') = e.symm(w')` (as `E`-elements).

`≤`: `i(w') = ⋃_{X ∈ w'} i(↑X) = ⋃_{X ∈ w'} e.symm(↑X)`, and each `e.symm(↑X) ≤ e.symm(w')` by
`principal_le_of_mem` and monotonicity of `e.symm`.

`≥`: the family `c(X) := e.symm(↑X)` (`X ∈ w'`) is directed with sup exactly `i(w')` (`hS_eq`
below, "for free" from the membership formula), hence `a`-fixed (`toElementMap_iSupDirected_fixed`).
Algebraicity of `w'` in `F` reduces `w' ≤ e(i(w'))` to checking `↑X ≤ e(i(w'))` for each `X ∈ w'`,
which (applying `e.symm`) is exactly `c(X) ≤ i(w')` — true since `i(w')` is the sup of the `c`
family. -/
theorem toElementMap_sectionMap (w' : F.Element) :
    (sectionMap e).toElementMap w' = (e.symm w').1 := by
  have hdirC : ∀ i j : {X : Set β // w'.mem X}, ∃ k : {X : Set β // w'.mem X},
      (e.symm (F.principal (w'.sub i.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 ∧
        (e.symm (F.principal (w'.sub j.2))).1 ≤ (e.symm (F.principal (w'.sub k.2))).1 :=
    fun i j => ⟨⟨i.1 ∩ j.1, w'.inter_mem i.2 j.2⟩,
      e.symm.monotone ((F.principal_le_iff (w'.sub i.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_left),
      e.symm.monotone ((F.principal_le_iff (w'.sub j.2) (w'.sub (w'.inter_mem i.2 j.2))).mpr
        Set.inter_subset_right)⟩
  have hS_eq : (sectionMap e).toElementMap w' =
      iSupDirected (fun i : {X : Set β // w'.mem X} => (e.symm (F.principal (w'.sub i.2))).1)
        hdirC := by
    apply Element.ext
    intro Z
    rw [toElementMap_mem_iff_principal, mem_iSupDirected]
    constructor
    · rintro ⟨X, hX, hZ⟩; rw [toElementMap_sectionMap_principal] at hZ; exact ⟨⟨X, hX⟩, hZ⟩
    · rintro ⟨⟨X, hX⟩, hZ⟩; exact ⟨X, hX, by rwa [toElementMap_sectionMap_principal]⟩
  have hfixC : ∀ i : {X : Set β // w'.mem X},
      a.toElementMap (e.symm (F.principal (w'.sub i.2))).1 =
        (e.symm (F.principal (w'.sub i.2))).1 :=
    fun i => (e.symm (F.principal (w'.sub i.2))).2
  apply le_antisymm
  · rw [hS_eq]
    apply iSupDirected_le
    intro i
    exact e.symm.monotone (principal_le_of_mem i.2)
  · have hSfix : a.toElementMap ((sectionMap e).toElementMap w') =
        (sectionMap e).toElementMap w' := by
      rw [hS_eq]; exact toElementMap_iSupDirected_fixed _ hdirC hfixC
    have key : w' ≤ e ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
      refine le_trans (le_of_eq (eq_iSupDirected_principal w'))
        (iSupDirected_le _ (principalFamily_directed w') ?_)
      intro i
      have : e.symm (F.principal (w'.sub i.2)) ≤ ⟨(sectionMap e).toElementMap w', hSfix⟩ := by
        show (e.symm (F.principal (w'.sub i.2))).1 ≤ (sectionMap e).toElementMap w'
        rw [hS_eq]
        exact le_iSupDirected _ hdirC i
      have := e.monotone this
      rwa [e.apply_symm_apply] at this
    have := e.symm.monotone key
    rwa [e.symm_apply_apply] at this
end HardDirection
end DomainTheory.Neighborhood
