module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixOfO

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap ApproximableMap₂

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

def strictEvalFade : ApproximableMap (prod (funSpace D E) D) E :=
  (fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))

def strictRetraction : ApproximableMap (funSpace D E) (funSpace D E) := curry strictEvalFade

theorem toApproxMap_strictRetraction_mem {φ : (funSpace D E).Element} {y : D.Element}
    {Z : Set β} :
    ((toApproxMap (strictRetraction.toElementMap φ)).toElementMap y).mem Z ↔
      E.mem Z ∧ (Z = E.master ∨ (y ≠ D.bot ∧ ((toApproxMap φ).toElementMap y).mem Z)) := by
  show ((toApproxMap ((curry strictEvalFade).toElementMap φ)).toElementMap y).mem Z ↔ _
  rw [toElementMap_curry_apply]
  show (((fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))).toElementMap
      (pair φ y)).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁, snd_pair,
    evalMap_apply, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

theorem strictRetraction_apply_bot (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap D.bot = E.bot := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hne, -⟩⟩
    · rfl
    · exact absurd rfl hne
  · rintro rfl
    exact ⟨E.master_mem, Or.inl rfl⟩

theorem isStrict_toApproxMap_of_fixed {φ : (funSpace D E).Element}
    (hφ : strictRetraction.toElementMap φ = φ) : Exercise510.IsStrict (toApproxMap φ) := by
  rw [Exercise510.isStrict_iff_apply_bot]
  have h := strictRetraction_apply_bot φ
  rwa [hφ] at h

theorem strictRetraction_apply_of_ne_bot {y : D.Element} (hy : y ≠ D.bot)
    (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap y
      = (toApproxMap φ).toElementMap y := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem]
  constructor
  · rintro ⟨-, rfl | ⟨-, hZ⟩⟩
    · exact ((toApproxMap φ).toElementMap y).master_mem
    · exact hZ
  · intro hZ
    exact ⟨((toApproxMap φ).toElementMap y).sub hZ, Or.inr ⟨hy, hZ⟩⟩

theorem toApproxMap_toFilter (f : ApproximableMap D E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv D E).right_inv f

theorem toFilter_toApproxMap (φ : (funSpace D E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv D E).left_inv φ

theorem strictRetraction_fixed_of_isStrict {f : ApproximableMap D E} (hf : Exercise510.IsStrict f) :
    strictRetraction.toElementMap (toFilter f) = toFilter f := by
  have hbot : f.toElementMap D.bot = E.bot := Exercise510.isStrict_iff_apply_bot.mp hf
  have key : toApproxMap (strictRetraction.toElementMap (toFilter f)) = f := by
    apply ext_of_toElementMap
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot, hbot]
    · rw [strictRetraction_apply_of_ne_bot hy, toApproxMap_toFilter]
  rw [← toFilter_toApproxMap (strictRetraction.toElementMap (toFilter f)), key]

def strictRetractionFixIso :
    {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ} ≃o
      Exercise510.StrictMap D E where
  toFun φ := ⟨toApproxMap φ.1, isStrict_toApproxMap_of_fixed φ.2⟩
  invFun f := ⟨toFilter f.1, strictRetraction_fixed_of_isStrict f.2⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ φ'
    show toApproxMap φ.1 ≤ toApproxMap φ'.1 ↔ φ.1 ≤ φ'.1
    exact (funSpaceEquiv D E).map_rel_iff

theorem strictRetraction_le_idMap : strictRetraction (D := D) (E := E) ≤ idMap (funSpace D E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap]
  have hmap : toApproxMap (strictRetraction.toElementMap φ) ≤ toApproxMap φ := by
    rw [le_iff_toElementMap_le]
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot]
      intro Z hZ
      rw [mem_bot] at hZ
      rw [hZ]
      exact ((toApproxMap φ).toElementMap D.bot).master_mem
    · rw [strictRetraction_apply_of_ne_bot hy]
  exact (funSpaceEquiv D E).map_rel_iff.mp hmap

theorem toApproxMap_injective {a b : (funSpace D E).Element} (h : toApproxMap a = toApproxMap b) :
    a = b := by
  rw [← toFilter_toApproxMap a, ← toFilter_toApproxMap b, h]

theorem isRetraction_strictRetraction : Retraction (strictRetraction (D := D) (E := E)) := by
  constructor
  apply ext_of_toElementMap
  intro φ
  rw [toElementMap_comp]
  apply toApproxMap_injective
  apply ext_of_toElementMap
  intro y
  by_cases hy : y = D.bot
  · rw [hy, strictRetraction_apply_bot, strictRetraction_apply_bot]
  · rw [strictRetraction_apply_of_ne_bot hy, strictRetraction_apply_of_ne_bot hy]

theorem example84b_strict :
    IsProjection (strictRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.strictFun D E).Element ≃o
        {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ}) :=
  ⟨⟨isRetraction_strictRetraction, strictRetraction_le_idMap⟩,
    ⟨strictRetractionFixIso.trans (Exercise510.strictFunEquiv D E).symm |>.symm⟩⟩
end

end DomainTheory.NeighbourhoodSystems
