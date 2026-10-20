/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition711
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Product
public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Proposition 7.12 (Scott 1981, PRG-19, §7) — the finite join map on `ℙ𝒟`

Scott states, right after Definition 7.11:

> **Proposition 7.12.** The mapping `λ x₀, …, x_{n-1}. {x₀, …, x_{n-1}} : Dⁿ → ℙD` is approximable
> and is computable if `D` is effectively given. Moreover, the map `λ x. {x}` shows that
> `D ⊴ ℙD`, and we also have `{x₀, …, x_{n-1}} = {x₀} ∩ … ∩ {x_{n-1}}` as an intersection of filters.

This file delivers Parts A, B, and D **in full**. Part C (`D ⊴ ℙD`) turns out to be **false in
general** under the present definition of `ℙ𝒟` (Definition 7.9), and we **formalize a
counterexample** instead — see `Counterexample712C` at the bottom.

## Part A — the singleton map `λ x. {x}` is approximable

Built by Exercise 2.8's `ofMono` from its values on principal inputs `↑X ↦ {↑X}` (`PDsingleton`).
Monotonicity uses that `{↑X'}` is *blunter* than `{↑X}` when `X' ⊆ X`.

On finite elements, `{↑X} = ↑(↓X)` in `ℙ𝒟` (`PDsingleton_principal`): the principal filter of the
down-set token `↓X`.

## Part B — the intersection law `{x, y} = {x} ∩ {y}` (hence the general fold)

Scott's proof on principal inputs `{↑X} ∩ {↑Y} = {↑X, ↑Y}` unfolds to
`↓X ∩ ↓Y = ↑(↓X ∩ ↓Y)` via `upSet_inter`, then to the binary join. The general law
`PDfinJoin_inter` follows by induction on `n`.

## Part C — `D ⊴ ℙD` is FALSE in general (counterexample)

Scott's closing remark "`λ x. {x}` shows `D ⊴ ℙD`" does **not** hold for an arbitrary neighbourhood
system `𝒟` once `ℙ𝒟` is taken to include the **empty union `∅`** (Definition 7.9's `n = 0` case,
`PDmem_empty`). The obstruction is structural:

* `ℙ𝒟` is **unconditionally** closed under intersection (`PDmem_inter`; the empty union always
  supplies the missing consistency witness), so `|ℙ𝒟|` has a **greatest element** — the improper
  filter consisting of *all* `ℙ𝒟`-neighbourhoods (`Counterexample712C.hasTop_of_inter_closed`).
* Any subsystem `D' ◁ ℙ𝒟` inherits that unconditional ∩-closure (`Definition 6.10`'s
  `inter_closed`), so `|D'|` **also** has a greatest element.
* `D ⊴ ℙ𝒟` means `D ≅ᴰ D'` for some `D' ◁ ℙ𝒟`, and `≅ᴰ` is an order-isomorphism of element
  lattices, which transports "has a greatest element" back to `|D|`.

So `D ⊴ ℙ𝒟` forces `|D|` to have a greatest element. But the two-point **flat** domain `Vshape`
(neighbourhoods `Δ = {true, false}`, `{true}`, `{false}`, with `{true} ∩ {false} = ∅ ∉ 𝒟`) has two
incomparable maximal elements and hence **no** greatest element. Therefore
`Vshape ⋬ Vshape.PowerDomain` (`Counterexample712C.vshape_not_trianglelefteq_powerDomain`).

This is exactly the wall the projection-pair route hit: a monotone (approximable) retraction
`ℙ𝒟 → 𝒟` would have to send `⊤_{ℙ𝒟} = ↑∅` to an upper bound of all of `|𝒟|`, i.e. to a greatest
element of `|𝒟|`, which need not exist. Scott's claim is correct precisely when `|𝒟|` has a top
(equivalently `𝒟` has a least neighbourhood), e.g. when `∅ ∈ 𝒟`; the singleton injection itself
(`PDsingletonApproxMap`) is the surviving "one half" of the would-be projection pair.

## Part D — computability when `D` is effectively given

Against `PDPresentation` (Proposition 7.10), the neighbourhood relation for `λ x. {x}` is
`∃ b ∈ dl k, X_n ⊆ X_b` — a bounded `∃` over `P.incl_computable` (`singleton_isComputable`).
The binary join map on `D × D` is obtained from two independent singleton conditions
(`PDfinJoinApproxMap₂_isComputable`); the general `n`-ary case reduces to the intersection law.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### Part A — the singleton approximable map. -/

/-- **Proposition 7.12 — monotonicity of `{·}` on principal inputs.** When `X' ⊆ X`, the join
`{↑X'}` is blunter than `{↑X}` in `|ℙ𝒟|`. -/
theorem PDsingleton_mono {X X' : Set α} (hX : V.mem X) (hX' : V.mem X') (hX'X : X' ⊆ X) :
    V.PDsingleton (V.principal hX) ≤ V.PDsingleton (V.principal hX') := by
  intro W hW
  rw [PDmem_singleton] at hW ⊢
  obtain ⟨Y, hYpr, hPD, hsub⟩ := hW
  rw [mem_principal] at hYpr
  exact ⟨Y, ⟨hYpr.1, hX'X.trans hYpr.2⟩, hPD, hsub⟩

/-- **Proposition 7.12 — the singleton approximable map `λ x. {x}`.** Built from Exercise 2.8's
extension principle: on the finite element `↑X` the value is `{↑X}`. -/
def PDsingletonApproxMap : ApproximableMap V V.PowerDomain :=
  ofMono (fun _X hX => V.PDsingleton (V.principal hX))
    (fun X X' hX hX' hX'X => @PDsingleton_mono α V X X' hX hX' hX'X)

@[simp] theorem PDsingletonApproxMap_rel {X : Set α} {W : Set (Set α)} (hX : V.mem X) :
    (PDsingletonApproxMap (V := V)).rel X W ↔ (V.PDsingleton (V.principal hX)).mem W := by
  dsimp [PDsingletonApproxMap, ofMono]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨hX, h⟩

/-! ### Part B — the intersection law. -/

/-- Meet of two `{·}`-values in `|ℙ𝒟|`. -/
def PDsingletonMeet (a b : V.PowerDomain.Element) : V.PowerDomain.Element where
  mem W := a.mem W ∧ b.mem W
  sub h := a.sub h.1
  master_mem := ⟨a.master_mem, b.master_mem⟩
  inter_mem h1 h2 := ⟨a.inter_mem h1.1 h2.1, b.inter_mem h1.2 h2.2⟩
  up_mem h hW hsub := ⟨a.up_mem h.1 hW hsub, b.up_mem h.2 hW hsub⟩

@[simp] theorem PDsingletonMeet_mem {a b : V.PowerDomain.Element} {W : Set (Set α)} :
    (V.PDsingletonMeet a b).mem W ↔ a.mem W ∧ b.mem W := Iff.rfl

/-! ### Part B continued — binary approximable join map. -/

/-- **Proposition 7.12 — the binary join as a two-variable approximable map.** -/
def PDfinJoinApproxMap₂ : ApproximableMap₂ V V V.PowerDomain where
  rel X Y W := (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W
  rel_dom₀ h := (PDsingletonApproxMap (V := V)).rel_dom h.1
  rel_dom₁ h := (PDsingletonApproxMap (V := V)).rel_dom h.2
  rel_cod h := (PDsingletonApproxMap (V := V)).rel_cod h.1
  master_rel := ⟨(PDsingletonApproxMap (V := V)).master_rel, (PDsingletonApproxMap (V := V)).master_rel⟩
  inter_right := fun ⟨h1, h2⟩ ⟨h1', h2'⟩ =>
    ⟨(PDsingletonApproxMap (V := V)).inter_right h1 h1',
      (PDsingletonApproxMap (V := V)).inter_right h2 h2'⟩
  mono := fun ⟨h1, h2⟩ hXX' hYY' hWW' hX' hY' hW' =>
    ⟨(PDsingletonApproxMap (V := V)).mono h1 hXX' hWW' hX' hW',
      (PDsingletonApproxMap (V := V)).mono h2 hYY' hWW' hY' hW'⟩

/-- **Proposition 7.12 — the binary join map on `D × D`.** -/
def finJoinMap_prod : ApproximableMap (prod V V) V.PowerDomain := ofMap₂ (PDfinJoinApproxMap₂ (V := V))

@[simp] theorem finJoinMap_prod_rel {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (finJoinMap_prod (V := V)).rel (prodNbhd X Y) W ↔
      (PDfinJoinApproxMap₂ (V := V)).rel X Y W := by
  dsimp [finJoinMap_prod, ofMap₂]
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨prod_mem_prodNbhd hX hY, h⟩⟩

/-! ### Part D — computability. -/

variable (P : ComputablePresentation V)

end NeighborhoodSystem

/-! ## Part C — counterexample: `D ⊴ ℙD` fails for the flat two-point domain.

The argument isolates a single domain invariant — *having a greatest element* — that `ℙ𝒟` (with the
empty union) always satisfies but a general `𝒟` need not, and that is preserved under both `◁` and
`≅ᴰ`. -/

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

/-- A domain *has a greatest element* if some element dominates every other. Order-isomorphisms and
the inclusion order on filters transport this property. -/
def HasTop (E : NeighborhoodSystem γ) : Prop := ∃ t : E.Element, ∀ x : E.Element, x ≤ t

/-- **The improper filter.** When a system `E` is *unconditionally* closed under intersection, the
family of *all* its neighbourhoods is a genuine filter — the greatest element of `|E|`. -/
def improperTop (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : E.Element where
  mem := E.mem
  sub h := h
  master_mem := E.master_mem
  inter_mem h1 h2 := hcl h1 h2
  up_mem _ hY _ := hY

/-! ### The flat two-point domain `Vshape`, with no greatest element. -/

/-- `{true} ∩ {false} = ∅` in `Set Bool`. -/
theorem tf_inter : ({true} : Set Bool) ∩ {false} = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h; exact absurd h (by decide)

/-- `{false} ∩ {true} = ∅` in `Set Bool`. -/
private theorem ft_inter : ({false} : Set Bool) ∩ {true} = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h; exact absurd h (by decide)

/-- The flat two-point domain over `Bool`: the neighbourhoods are the master `Δ = {true, false}`
and the two singletons `{true}`, `{false}`. Since `{true} ∩ {false} = ∅` and `∅` is not a
neighbourhood (and has no neighbourhood subset), condition (ii) holds only vacuously there — this is
a genuine Scott neighbourhood system whose two singletons are *inconsistent*. -/
def Vshape : NeighborhoodSystem Bool where
  mem X := X = Set.univ ∨ X = {true} ∨ X = {false}
  master := Set.univ
  master_nonempty := ⟨true, Set.mem_univ _⟩
  master_mem := Or.inl rfl
  sub_master _ := Set.subset_univ _
  inter_mem := by
    rintro X Y Z hX hY hZ hZsub
    -- every neighbourhood is nonempty, so a witness `Z ⊆ X ∩ Y = ∅` is impossible
    have hZne : Z.Nonempty := by
      rcases hZ with rfl | rfl | rfl
      · exact ⟨true, Set.mem_univ true⟩
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    obtain ⟨z, hz⟩ := hZne
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inr (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inl (by rw [Set.inter_univ]))
    · exact Or.inr (Or.inl (by rw [Set.inter_self]))
    · rw [tf_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_univ]))
    · rw [ft_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_self]))
end Counterexample712C
end DomainTheory.Neighborhood
