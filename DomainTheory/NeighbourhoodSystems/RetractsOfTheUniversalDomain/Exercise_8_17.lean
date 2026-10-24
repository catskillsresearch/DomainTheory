module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_27
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
/- concordance: source L5173 EXERCISE 8.17 explicit embeddings into U -/
-- Exercise817/ProjPair.lean
universe u v w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **A heterogeneous projection pair** — the raw data `Lemma615.trianglelefteq_of_projectionPair`
consumes, bundled for easy composition. -/
structure ProjPair (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Universality, as an abstract predicate**: every countable neighbourhood system embeds
(up to isomorphism) as a subsystem of `W` — Theorem 8.8(a)'s property, extracted from the specific
domain `𝒰` to an arbitrary `W`. -/
def IsUniversal {δ : Type w} (W : NeighborhoodSystem δ) : Prop :=
  ∀ {α : Type u} (D : NeighborhoodSystem α) [Countable {S : Set α // D.mem S}], D ⊴ W
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **`ProjPair`s compose.** If `D ⇄ E` and `E ⇄ F` are projection pairs, so is `D ⇄ F`
(`inj := p2.inj ∘ p1.inj`, `proj := p1.proj ∘ p2.proj`). The first law composes as an equality
chain; the second only needs `≤`, transported through `comp_mono_gen`. -/
def ProjPair.comp {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (p1 : ProjPair D E) (p2 : ProjPair E F) :
    ProjPair D F where
  inj := p2.inj.comp p1.inj
  proj := p1.proj.comp p2.proj
  proj_comp_inj := by
    show (p1.proj.comp p2.proj).comp (p2.inj.comp p1.inj) = idMap D
    rw [comp_assoc, ← comp_assoc p2.proj p2.inj p1.inj, p2.proj_comp_inj, idMap_comp,
      p1.proj_comp_inj]
  inj_comp_proj_le := by
    show (p2.inj.comp p1.inj).comp (p1.proj.comp p2.proj) ≤ idMap F
    rw [comp_assoc, ← comp_assoc p1.inj p1.proj p2.proj]
    calc p2.inj.comp ((p1.inj.comp p1.proj).comp p2.proj)
        ≤ p2.inj.comp ((idMap E).comp p2.proj) :=
          comp_mono_gen le_rfl (comp_mono_gen p1.inj_comp_proj_le le_rfl)
      _ = p2.inj.comp p2.proj := by rw [idMap_comp]
      _ ≤ idMap F := p2.inj_comp_proj_le
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **A `DomainIso` gives a `ProjPair`, via Theorem 2.7's `ofIso`.** Both round trips are genuine
*equalities* (not just `≤`), since `e` is a full isomorphism, not merely a retraction. Uses
`le_iff_toElementMap_le` (choice-free) rather than the classical `ext_of_toElementMap` — matching
`Theorem86.lean`'s `isRetraction_subApprox`, which flags the same discipline. -/
def ProjPair.ofIso {D : NeighborhoodSystem α} {E : NeighborhoodSystem β} (e : DomainIso D E) :
    ProjPair D E where
  inj := ApproximableMap.ofIso e
  proj := ApproximableMap.ofIso e.symm
  proj_comp_inj := by
    have heq : ∀ x, ((ApproximableMap.ofIso e.symm).comp (ApproximableMap.ofIso e)).toElementMap x
        = (idMap D).toElementMap x := by
      intro x
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
        toElementMap_idMap]
    exact le_antisymm (le_iff_toElementMap_le.mpr fun x => (heq x).le)
      (le_iff_toElementMap_le.mpr fun x => (heq x).ge)
  inj_comp_proj_le := by
    have heq : ∀ y, ((ApproximableMap.ofIso e).comp (ApproximableMap.ofIso e.symm)).toElementMap y
        = (idMap E).toElementMap y := by
      intro y
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
        toElementMap_idMap]
    exact le_iff_toElementMap_le.mpr fun y => (heq y).le
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **A subsystem relation `D ◁ E` gives a `ProjPair`** (Proposition 6.12, rebundled). -/
def ProjPair.ofSubsystem {D E : NeighborhoodSystem α} (h : D ◁ E) : ProjPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **`D ⊴ E` composed with an isomorphism `D ≅ᴰ D'` on the left is still `D ⊴ E`** — immediate
from unfolding `⊴` and composing the two `DomainIso`s (`OrderIso.trans`). -/
theorem trianglelefteq_of_isomorphic_left {D : NeighborhoodSystem α} {D' : NeighborhoodSystem β}
    {E : NeighborhoodSystem γ} (hDD' : D ≅ᴰ D') (hD'E : D' ⊴ E) : D ⊴ E := by
  obtain ⟨F, hFE, ⟨eD'F⟩⟩ := hD'E
  obtain ⟨eDD'⟩ := hDD'
  exact ⟨F, hFE, ⟨eDD'.trans eD'F⟩⟩

/-- **`⊴` is transitive.** `D ⊴ E` and `E ⊴ F` give `D ⊴ F`: unfold both to a subsystem `D' ◁ E`
(`D ≅ᴰ D'`) and `E' ◁ F` (`E ≅ᴰ E'`); `ProjPair.ofSubsystem` turns `D' ◁ E`/`E' ◁ F` into projection
pairs, `ProjPair.ofIso` turns `E ≅ᴰ E'` into one too, and composing all three (`ProjPair.comp`) gives
a projection pair `D' ⇄ F`, hence `D' ⊴ F` (Lemma 6.15). Gluing back `D ≅ᴰ D'` on the left
(`trianglelefteq_of_isomorphic_left`) finishes. -/
theorem trianglelefteq_trans {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (h1 : D ⊴ E) (h2 : E ⊴ F) : D ⊴ F := by
  obtain ⟨D', hD'E, ⟨eDD'⟩⟩ := h1
  obtain ⟨E', hE'F, ⟨eEE'⟩⟩ := h2
  have pD'F : ProjPair D' F :=
    ((ProjPair.ofSubsystem hD'E).comp (ProjPair.ofIso eEE')).comp (ProjPair.ofSubsystem hE'F)
  have hD'F : D' ⊴ F :=
    trianglelefteq_of_projectionPair pD'F.inj pD'F.proj pD'F.proj_comp_inj pD'F.inj_comp_proj_le
  exact trianglelefteq_of_isomorphic_left ⟨eDD'⟩ hD'F
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **`𝒰` is universal** (restating Theorem 8.8(a) in `⊴`-shape). -/
theorem U_isUniversal : IsUniversal.{u} U := by
  intro α D _
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Exercise 8.17, Part 1 (`→`).** `iArrow/jArrow` already are the pair `𝒰→𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem funSpaceUU_trianglelefteq_U : funSpace U U ⊴ U :=
  trianglelefteq_of_projectionPair iArrow jArrow jArrow_comp_iArrow iArrow_comp_jArrow_le
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Universality transports along isomorphism.** If `W` is universal and `W ≅ᴰ W'`, then `W'` is
universal too: every countable `D` embeds in `W` (`D ⊴ W`), and `W ⊴ W'` (take `D' := W'` in `⊴`'s
definition, using `Subsystem.refl` and the given isomorphism), so `trianglelefteq_trans` finishes. -/
theorem isUniversal_of_isomorphic {W : NeighborhoodSystem β} {W' : NeighborhoodSystem γ}
    (hW : IsUniversal.{u} W) (hWW' : W ≅ᴰ W') : IsUniversal.{u} W' := by
  have hWW'_tri : W ⊴ W' := hWW'.elim fun e => ⟨W', Subsystem.refl W', ⟨e⟩⟩
  intro α D _
  exact trianglelefteq_trans (hW D) hWW'_tri
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Exercise 8.17, Part 3.** Exercise 8.12's `V` (a `NeighborhoodSystem ℕ`, built from `2^kℕ+ℓ` —
literally a *different* neighbourhood system from `U : NeighborhoodSystem ℚ`, not merely a
relabelling) is a universal domain, since it is effectively isomorphic to `𝒰` (`effectiveIso812_UV`,
Exercise 8.12's headline) and universality transports along isomorphism. -/
theorem V_isUniversal : IsUniversal.{u} V :=
  isUniversal_of_isomorphic U_isUniversal ⟨effectiveIso812_UV.toDomainIso⟩
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Exercise 8.17, Part 1 (`×`).** `iTimes/jTimes` already are the pair `𝒰×𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem prodUU_trianglelefteq_U : prod U U ⊴ U :=
  trianglelefteq_of_projectionPair iTimes jTimes jTimes_comp_iTimes iTimes_comp_jTimes_le
end

section
open NeighborhoodSystem ApproximableMap Subsystem
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Exercise 8.17, Part 1 (`+`).** `iPlus/jPlus` (`Definition89.lean`) already *are* the computable
projection pair `𝒰+𝒰 ⇄ 𝒰` needed for 8.9. Bonus: Lemma 6.15 upgrades it to `𝒰+𝒰 ⊴ 𝒰`. -/
theorem sumUU_trianglelefteq_U : sum U U U_mem_nonempty U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iPlus jPlus jPlus_comp_iPlus iPlus_comp_jPlus_le
end

section
set_option linter.unusedVariables false

theorem example_817.{u} : And
  (And
    (And (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U))
    (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Sum.{0, 0} Rat Rat) Rat
      (@DomainTheory.NeighbourhoodSystems.prod.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
      DomainTheory.NeighbourhoodSystems.U))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Option.{0} (Sum.{0, 0} Rat Rat)) Rat
    (@DomainTheory.NeighbourhoodSystems.sum.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U_mem_nonempty
      DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
    DomainTheory.NeighbourhoodSystems.U) :=
  @And.intro
  (And
    (And (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U))
    (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Sum.{0, 0} Rat Rat) Rat
      (@DomainTheory.NeighbourhoodSystems.prod.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
      DomainTheory.NeighbourhoodSystems.U))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Option.{0} (Sum.{0, 0} Rat Rat)) Rat
    (@DomainTheory.NeighbourhoodSystems.sum.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U_mem_nonempty
      DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
    DomainTheory.NeighbourhoodSystems.U)
  (@And.intro
    (And (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U))
    (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Sum.{0, 0} Rat Rat) Rat
      (@DomainTheory.NeighbourhoodSystems.prod.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
      DomainTheory.NeighbourhoodSystems.U)
    (@And.intro (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U)
      (@DomainTheory.NeighbourhoodSystems.V_isUniversal.{u})
      DomainTheory.NeighbourhoodSystems.funSpaceUU_trianglelefteq_U)
    DomainTheory.NeighbourhoodSystems.prodUU_trianglelefteq_U)
  DomainTheory.NeighbourhoodSystems.sumUU_trianglelefteq_U
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Reading off the pair from a function `T → E`.** `funToPair(φ) = (φ(true), φ(false))`. -/
noncomputable def funToPair : ApproximableMap (funSpace TD E) (prod E E) :=
  paired
    ((evalMap TD E).comp
      (paired (idMap (funSpace TD E)) (constMap (funSpace TD E) Example23.trueElt)))
    ((evalMap TD E).comp
      (paired (idMap (funSpace TD E)) (constMap (funSpace TD E) Example23.falseElt)))

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)

/-- **The tagging embedding `E + E → T × (E × E)`.** `w ↦ (which w, out₀ w, out₁ w)`. -/
noncomputable def sumToProdT : ApproximableMap (sum E E hE hE) (prod TD (prod E E)) :=
  paired (whichMap E E hE hE)
    (paired (outMap₀ (h₀ := hE) (h₁ := hE)) (outMap₁ (h₀ := hE) (h₁ := hE)))

end Sum
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- The "swap" map `(E×E)×T → T×(E×E)`, used to feed `cond`'s `T×E×E`-shaped domain from a
`(E×E)×T`-shaped one so it can be curried away from the `T`-argument. -/
noncomputable def swapProdT : ApproximableMap (prod (prod E E) TD) (prod TD (prod E E)) :=
  paired (proj₁ (prod E E) TD) (proj₀ (prod E E) TD)

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Pairing up, as a function out of `T`.** `pairToFun(x, y) : T → E` sends `t ↦ cond(t, x,
y)`; in particular `true ↦ x`, `false ↦ y`, `⊥ ↦ ⊥` (Exercise 3.26). -/
noncomputable def pairToFun : ApproximableMap (prod E E) (funSpace TD E) :=
  curry ((cond E).comp swapProdT)

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- **`TD.bot = Example23.botElt`.** These are the *same* element (`TD` and `Example23.T` are both
`Example12.neighborhoodSystem`), but not syntactically unifiable by `rfl` (the `abbrev`s don't
delta-reduce transparently through `NeighborhoodSystem.bot`'s field projection), so we prove it by
antisymmetry instead. -/
theorem TD_bot_eq_botElt : TD.bot = Example23.botElt :=
  le_antisymm (NeighborhoodSystem.bot_le _ _) (Example23.botElt_le _)

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

/-- **`T`'s elements, named via `Example23`.** The three-way classification of `Example12`,
restated with `Example23`'s `⊥`/`true`/`false` names (they are the *same* terms by `rfl`). -/
theorem TD_trichotomy (t : TD.Element) :
    t = Example23.botElt ∨ t = Example23.trueElt ∨ t = Example23.falseElt :=
  Example12.neighborhoodSystem.element_classification t
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- **`expMap` is monotone in its contravariant argument** (`k` fixed): `h ≤ h' ⟹ expMap h k ≤
expMap h' k`. Proved choice-freely from `comp_mono_gen` and the order-isomorphism `funSpaceEquiv`,
transported through the elementwise formula `toApproxMap_toElementMap_expMap`. -/
theorem expMap_mono_left {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β}
    {V0' : NeighborhoodSystem γ} {V1' : NeighborhoodSystem δ}
    {h h' : ApproximableMap V0' V0} (hh : h ≤ h') (k : ApproximableMap V1 V1') :
    expMap h k ≤ expMap h' k := by
  rw [le_iff_toElementMap_le]
  intro φ
  apply (funSpaceEquiv V0' V1').map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap_expMap,
    toApproxMap_toElementMap_expMap]
  exact comp_mono_gen le_rfl (comp_mono_gen le_rfl hh)

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- **Contravariant functoriality of `⊴` in the function-space's domain argument.** `A ⊴ B ⟹
(A → C) ⊴ (B → C)` for any `C`: precompose/postcompose with the given projection pair via
`expMap`. -/
theorem funSpace_dom_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : funSpace A C ⊴ funSpace B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (expMap p.proj (idMap C)) (expMap p.inj (idMap C))
    ?_ ?_
  · have hcomp := (expMap_comp p.proj (idMap C) p.inj (idMap C)).symm
    rw [hcomp, p.proj_comp_inj, idMap_comp]
    exact expMap_id
  · calc (expMap p.proj (idMap C)).comp (expMap p.inj (idMap C))
        = expMap (p.inj.comp p.proj) ((idMap C).comp (idMap C)) :=
          (expMap_comp p.inj (idMap C) p.proj (idMap C)).symm
      _ ≤ expMap (idMap B) ((idMap C).comp (idMap C)) :=
          expMap_mono_left p.inj_comp_proj_le _
      _ = expMap (idMap B) (idMap C) := by rw [idMap_comp]
      _ = idMap (funSpace B C) := expMap_id

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **`out₀ ∘ in₁ = const ⊥`.** A right-injected element carries no left-hand information. -/
theorem outMap₀_comp_inMap₁ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁)) = constMap V₁ V₀.bot := by
  apply ApproximableMap.ext
  intro Y Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hY, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, ?_⟩
    obtain ⟨b, hb⟩ := h₁ Y hY
    have hmaster : leftPart V₀ (inj₁ Y) ⊆ leftPart V₀ W := leftPart_mono V₀ hinj
    rw [leftPart_inj₁ V₀ ⟨b, hb⟩] at hmaster
    exact Set.Subset.antisymm (V₀.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hY, rfl⟩
    exact ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), V₀.master_mem, (leftPart_inj₁ V₀ (h₁ Y hY)).subset⟩

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **`out₁ ∘ in₀ = const ⊥`.** A left-injected element carries no right-hand information. -/
theorem outMap₁_comp_inMap₀ :
    (outMap₁ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁)) = constMap V₀ V₁.bot := by
  apply ApproximableMap.ext
  intro X Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hX, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hX, ?_⟩
    obtain ⟨a, ha⟩ := h₀ X hX
    have hmaster : rightPart V₁ (inj₀ X) ⊆ rightPart V₁ W := rightPart_mono V₁ hinj
    rw [rightPart_inj₀ V₁ ⟨a, ha⟩] at hmaster
    exact Set.Subset.antisymm (V₁.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hX, rfl⟩
    exact ⟨inj₀ X, ⟨hX, Or.inr (Or.inl ⟨X, hX, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, hX, rfl⟩), V₁.master_mem, (rightPart_inj₀ V₁ (h₀ X hX)).subset⟩

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- The pairing of two bottoms is the bottom of the product. -/
theorem pair_bot {V0 : NeighborhoodSystem α} {V1 : NeighborhoodSystem β} :
    pair V0.bot V1.bot = (prod V0 V1).bot := by
  apply le_antisymm
  · intro W hW
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW
    rw [mem_bot] at hX hY
    subst hX; subst hY
    rw [mem_bot]
    exact prod_master.symm
  · exact NeighborhoodSystem.bot_le _ _

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- **Covariant functoriality of `⊴` in `prod`'s left argument.** `A ⊴ B ⟹ prod A C ⊴ prod B C`
for any `C`: pair the given projection pair with the identity on `C`. -/
theorem prod_left_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : prod A C ⊴ prod B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (paired (p.inj.comp (proj₀ A C)) (proj₁ A C))
    (paired (p.proj.comp (proj₀ B C)) (proj₁ B C)) ?_ ?_
  · apply ext_of_toElementMap
    intro z
    rw [← pair_fst_snd z]
    set x := z.fst; set y := z.snd
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_paired,
      toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair,
      toElementMap_comp, toElementMap_proj₀, fst_pair, toElementMap_proj₁, snd_pair]
    have hxx : (p.proj.comp p.inj).toElementMap x = (idMap A).toElementMap x := by
      rw [p.proj_comp_inj]
    rw [toElementMap_comp, toElementMap_idMap] at hxx
    rw [hxx]
  · rw [le_iff_toElementMap_le]
    intro z
    rw [← pair_fst_snd z]
    set x := z.fst; set y := z.snd
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_paired,
      toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair,
      toElementMap_comp, toElementMap_proj₀, fst_pair, toElementMap_proj₁, snd_pair]
    apply pair_le_pair_iff.mpr
    refine ⟨?_, le_refl y⟩
    have hxx : (p.inj.comp p.proj).toElementMap x ≤ (idMap B).toElementMap x :=
      le_iff_toElementMap_le.mp p.inj_comp_proj_le x
    rwa [toElementMap_comp, toElementMap_idMap] at hxx

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- **Covariant functoriality of `⊴` in `prod`'s right argument.** `A ⊴ B ⟹ prod C A ⊴ prod C B`,
obtained from `prod_left_trianglelefteq` by conjugating with `prod`'s commutativity
(`Exercise315.prod_comm_isomorphic`). -/
theorem prod_right_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : prod C A ⊴ prod C B := by
  have h1 : prod C A ⊴ prod A C :=
    (prod_comm_isomorphic (V₀ := C) (V₁ := A)).elim fun e => ⟨_, Subsystem.refl _, ⟨e⟩⟩
  have h2 : prod A C ⊴ prod B C := prod_left_trianglelefteq C h
  have h3 : prod B C ⊴ prod C B :=
    (prod_comm_isomorphic (V₀ := B) (V₁ := C)).elim fun e => ⟨_, Subsystem.refl _, ⟨e⟩⟩
  exact trianglelefteq_trans (trianglelefteq_trans h1 h2) h3

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section General

variable {α β γ δ : Type*}

/-- If `f` sends the master input to only the master output, then `f` sends `⊥` to `⊥`
(more precisely, `≤ ⊥`, i.e. `= ⊥` by `bot_le`). The elementwise membership at `⊥` is read off the
relation at `V₀.master` via `rel_iff_mem_principal` (`⊥ = ↑Δ`). -/
theorem toElementMap_bot_le {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) (h : ∀ {Y}, f.rel V₀.master Y → Y = V₁.master) :
    f.toElementMap V₀.bot ≤ V₁.bot := by
  intro Y hY
  rw [mem_bot]
  exact h ((rel_iff_mem_principal f V₀.master_mem).mpr hY)

end General
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `out₀(⊥) ≤ ⊥`: the basepoint carries no left-hand information. -/
theorem outMap₀_bot_le :
    (outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₀.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₀.sub_master hg.2.1) ?_
  have h2 : leftPart V₀ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [leftPart_sumMaster] at h2

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `out₁(⊥) ≤ ⊥`: the basepoint carries no right-hand information. -/
theorem outMap₁_bot_le :
    (outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ V₁.bot := by
  refine toElementMap_bot_le _ ?_
  intro Y hg
  refine Set.Subset.antisymm (V₁.sub_master hg.2.1) ?_
  have h2 : rightPart V₁ (sumMaster V₀ V₁) ⊆ Y := hg.2.2
  rwa [rightPart_sumMaster] at h2

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


theorem toElementMap_funToPair (φ : (funSpace TD E).Element) :
    (funToPair (E := E)).toElementMap φ
      = pair ((toApproxMap φ).toElementMap Example23.trueElt)
          ((toApproxMap φ).toElementMap Example23.falseElt) := by
  simp only [funToPair, toElementMap_paired, toElementMap_comp, toElementMap_idMap,
    toElementMap_constMap, evalMap_apply]

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


theorem toElementMap_sumToProdT (w : (sum E E hE hE).Element) :
    (sumToProdT hE).toElementMap w
      = pair ((whichMap E E hE hE).toElementMap w)
          (pair ((outMap₀ (h₀ := hE) (h₁ := hE)).toElementMap w)
            ((outMap₁ (h₀ := hE) (h₁ := hE)).toElementMap w)) := by
  simp only [sumToProdT, toElementMap_paired]

end Sum
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`condSum ∘ sumToProdT = I`.** Scott's identity `cond_which`, transported through
`condSumEmb`. -/
theorem condSum_comp_sumToProdT :
    (condSum E E hE hE).comp (sumToProdT hE) = idMap (sum E E hE hE) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_sumToProdT, condSum, toElementMap_comp,
    condSumEmb_toElementMap]
  exact cond_which w

end Sum
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


theorem toElementMap_swapProdT (x y : E.Element) (t : TD.Element) :
    (swapProdT (E := E)).toElementMap (pair (pair x y) t) = pair t (pair x y) := by
  simp only [swapProdT, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁, fst_pair,
    snd_pair]

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


theorem toApproxMap_pairToFun (x y : E.Element) (t : TD.Element) :
    (toApproxMap ((pairToFun (E := E)).toElementMap (pair x y))).toElementMap t
      = (cond E).toElementMap (pair t (pair x y)) := by
  rw [pairToFun, toElementMap_curry_apply, toElementMap_comp, toElementMap_swapProdT]

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **`funToPair ∘ pairToFun = I`.** `(x, y) ↦ (λt. cond(t,x,y)) ↦ (cond(true,x,y),
cond(false,x,y)) = (x, y)`. -/
theorem funToPair_comp_pairToFun : (funToPair (E := E)).comp pairToFun = idMap (prod E E) := by
  apply ext_of_toElementMap
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair, toApproxMap_pairToFun,
    toApproxMap_pairToFun, Exercise326.cond_true, Exercise326.cond_false]

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **`pairToFun ∘ funToPair ≤ I`.** For every `φ : T → E`, feeding `(φ(true), φ(false))` back
through `cond` gives a map agreeing with `φ` at `true`/`false` and `≤ φ` at `⊥` (`E.bot ≤`
anything). Case split on `T`'s three elements (`TD_trichotomy`). -/
theorem pairToFun_comp_funToPair_le :
    (pairToFun (E := E)).comp funToPair ≤ idMap (funSpace TD E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair]
  apply (funSpaceEquiv TD E).map_rel_iff.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, le_iff_toElementMap_le]
  intro t
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [toApproxMap_pairToFun, Exercise326.cond_bot]; exact E.bot_le _
  · rw [toApproxMap_pairToFun, Exercise326.cond_true]
  · rw [toApproxMap_pairToFun, Exercise326.cond_false]

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **`E × E ⊴ (T → E)`.** -/
theorem prod_trianglelefteq_funSpace_TD : prod E E ⊴ funSpace TD E :=
  trianglelefteq_of_projectionPair pairToFun funToPair funToPair_comp_pairToFun
    pairToFun_comp_funToPair_le

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **Exercise 8.19, Goal 1.** `T ⊴ E` and `E → E ⊴ E` give `E × E ⊴ E`: chain `E×E ⊴ (T→E) ⊴
(E→E) ⊴ E`. -/
theorem prod_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    prod E E ⊴ E :=
  trianglelefteq_trans
    (trianglelefteq_trans prod_trianglelefteq_funSpace_TD (funSpace_dom_trianglelefteq E hT))
    hArrow

end Prod
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(⊥) ≤ ⊥`: the basepoint carries no tag information. Only the third `whichGuard` disjunct
applies at `W = (sum V₀ V₁ h₀ h₁).master`, forcing the output to `master`. -/
theorem which_bot_le :
    (whichMap V₀ V₁ h₀ h₁).toElementMap (sum V₀ V₁ h₀ h₁).bot ≤ Example23.botElt := by
  rw [← TD_bot_eq_botElt]
  refine toElementMap_bot_le _ ?_
  intro Y hg
  exact whichGuard_masterC hg.2.2 rfl

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(in₀ x) ≤ true`: a left-injected element's tag never reaches `false`. -/
theorem which_inMap₀_le_trueElt (x : V₀.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
      ≤ Example23.trueElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)).sub hZ) with rfl | rfl | rfl
  · exact Example23.trueElt.master_mem
  · show Example23.trueElt.mem Example12.zero
    exact Or.inr rfl
  · exfalso
    obtain ⟨Y, hY, hmem⟩ := which_mem_one.mp hZ
    obtain ⟨X, _, hX0, _, hsub⟩ := hmem
    exact not_inj₀_subset_inj₁ (h₀ X hX0) hsub

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326

section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(in₁ y) ≤ false`: a right-injected element's tag never reaches `true`. -/
theorem which_inMap₁_le_falseElt (y : V₁.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)
      ≤ Example23.falseElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)).sub hZ) with rfl | rfl | rfl
  · exact Example23.falseElt.master_mem
  · exfalso
    obtain ⟨X, hX, hmem⟩ := which_mem_zero.mp hZ
    obtain ⟨Y, _, hY0, _, hsub⟩ := hmem
    exact not_inj₁_subset_inj₀ (h₁ Y hY0) hsub
  · show Example23.falseElt.mem Example12.one
    exact Or.inr rfl

end SumHelpers
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`sumToProdT ∘ condSum ≤ I`.** Case-split `t : T` into `⊥ / true / false`
(`TD_trichotomy`); `condSum(t,x,y)` reduces to a concrete sum element (`⊥`, `in₀ x`, or `in₁ y`)
whose image under `sumToProdT` is read off via the round-trips
`outMap₀_comp_inMap₀`/`outMap₁_comp_inMap₀` (and their mirror images) together with the tag bounds
`which_inMap₀_le_trueElt`/`which_inMap₁_le_falseElt`. -/
theorem sumToProdT_comp_condSum_le :
    (sumToProdT hE).comp (condSum E E hE hE) ≤ idMap (prod TD (prod E E)) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [← pair_fst_snd z, ← pair_fst_snd z.snd]
  set t := z.fst; set x := z.snd.fst; set y := z.snd.snd
  clear_value t x y
  rw [toElementMap_comp, toElementMap_idMap]
  rcases TD_trichotomy t with rfl | rfl | rfl
  · rw [condSum_bot, toElementMap_sumToProdT]
    exact pair_le_pair_iff.mpr ⟨which_bot_le,
      pair_le_pair_iff.mpr ⟨outMap₀_bot_le.trans (E.bot_le x), outMap₁_bot_le.trans (E.bot_le y)⟩⟩
  · rw [condSum_true, toElementMap_sumToProdT]
    refine pair_le_pair_iff.mpr ⟨which_inMap₀_le_trueElt x, pair_le_pair_iff.mpr ⟨?_, ?_⟩⟩
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap x)
        (outMap₀_comp_inMap₀ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_idMap] at h2
      exact h2.le
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap x)
        (outMap₁_comp_inMap₀ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_constMap] at h2
      rw [h2]; exact E.bot_le _
  · rw [condSum_false, toElementMap_sumToProdT]
    refine pair_le_pair_iff.mpr ⟨which_inMap₁_le_falseElt y, pair_le_pair_iff.mpr ⟨?_, ?_⟩⟩
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap y)
        (outMap₀_comp_inMap₁ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_constMap] at h2
      rw [h2]; exact E.bot_le _
    · have h2 := congrArg (fun (f : ApproximableMap E E) => f.toElementMap y)
        (outMap₁_comp_inMap₁ (h₀ := hE) (h₁ := hE))
      simp only [toElementMap_comp, toElementMap_idMap] at h2
      exact h2.le

end Sum
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **`E + E ⊴ T × (E × E)`.** -/
theorem sum_trianglelefteq_prodT : sum E E hE hE ⊴ prod TD (prod E E) :=
  trianglelefteq_of_projectionPair (sumToProdT hE) (condSum E E hE hE) (condSum_comp_sumToProdT hE)
    (sumToProdT_comp_condSum_le hE)

end Sum
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **Exercise 8.19, Goal 2.** `T ⊴ E` and `E → E ⊴ E` give `E + E ⊴ E`: chain
`E+E ⊴ T×(E×E) ⊴ E×(E×E) ⊴ E×E ⊴ E`, using Goal 1 (applied twice, to peel off each product layer)
for the last two links. -/
theorem sum_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E := by
  have hPE : prod E E ⊴ E := prod_trianglelefteq_of hT hArrow
  exact trianglelefteq_trans
    (trianglelefteq_trans (sum_trianglelefteq_prodT hE) (prod_left_trianglelefteq (prod E E) hT))
    (trianglelefteq_trans (prod_right_trianglelefteq E hPE) hPE)

end Sum
end

section
open NeighborhoodSystem ApproximableMap Exercise326
universe u

end
end DomainTheory.NeighbourhoodSystems
end
