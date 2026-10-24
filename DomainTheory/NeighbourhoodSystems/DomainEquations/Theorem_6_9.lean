module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_6
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_8

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510
section
variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
/- concordance: source L3775 THEOREM 6.9 homomorphism from initial algebra -/
/-- **Theorem 6.9 (Scott 1981, PRG-19).** If `T` is continuous on maps and `D ≅ T(D)` (so `D` is a
`T`-algebra via `i : T(D) → D`), then for any `T`-algebra `B = (E, k)` with `k` strict there is a
homomorphism `D → E`. The homomorphism is the least fixed point of `λh. k ∘ T(h) ∘ j`. -/
theorem nonempty_algHom_of_continuousOnMaps
    (T : Endofunctor DomainObj) (hT : ContinuousOnMaps T)
    {D : DomainObj} (iso : Iso (T.obj D) D)
    (B : TAlgebra T) (hk : IsStrict B.str) :
    Nonempty {g : AlgHom (⟨D, iso.hom⟩ : TAlgebra T) B // IsStrict g.hom} := by
  -- `j = i⁻¹` is strict (it is an isomorphism of domains).
  have hji : iso.inv.comp iso.hom = idMap (T.obj D).sys := iso.hom_inv_id
  have hj : IsStrict iso.inv := isStrict_of_comp_eq_id hji
  -- Definition 6.8's witness that `λf. T(f)` is approximable.
  obtain ⟨Φ, hΦ⟩ := hT D B.carrier
  -- the operator `Op = (k ∘ · ∘ j) ∘ T` and its least fixed point.
  set Op := (homOp T D B.carrier iso.inv B.str hj hk).comp Φ with hOp
  set x := Op.fixElement with hx
  set h := toStrictMap x with hh
  let Tg : StrictMap (T.obj D).sys (T.obj B.carrier).sys :=
    ⟨T.map (X := D) (Y := B.carrier) h.1, hT.isStrict_map (D := D) (E := B.carrier) h⟩
  have hfix : Op.toElementMap x = x := toElementMap_fixElement Op
  have hxh : toStrictFilter h = x := toStrictFilter_toStrictMap x
  -- `Φ` sends `h` to the filter of `T(h)`.
  have hTg : toStrictMap (Φ.toElementMap (toStrictFilter h)) = Tg := Subtype.ext (hΦ h)
  have hφ : Φ.toElementMap (toStrictFilter h) = toStrictFilter Tg := by
    rw [← hTg]; exact (toStrictFilter_toStrictMap _).symm
  -- evaluate the operator at the fixed point.
  have hOpx : Op.toElementMap x
      = toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg) := by
    rw [hOp, toElementMap_comp, ← hxh, hφ, homOp_apply_filter]
  have hcompeq : toStrictFilter (homOpComp T D B.carrier iso.inv B.str hj hk Tg)
      = toStrictFilter h := by
    rw [← hOpx, hfix, hxh]
  have hh' : homOpComp T D B.carrier iso.inv B.str hj hk Tg = h := by
    have h2 := congrArg toStrictMap hcompeq
    rwa [toStrictMap_toStrictFilter, toStrictMap_toStrictFilter] at h2
  -- the fixed-point equation `h = k ∘ T(h) ∘ j`.
  have hcore : B.str.comp ((T.map (X := D) (Y := B.carrier) h.1).comp iso.inv) = h.1 :=
    congrArg Subtype.val hh'
  -- rearrange to the homomorphism square `h ∘ i = k ∘ T(h)`.
  refine ⟨⟨{ hom := h.1, comm := ?_ }, h.2⟩⟩
  show h.1.comp iso.hom = B.str.comp (T.map (X := D) (Y := B.carrier) h.1)
  conv_lhs => rw [← hcore]
  rw [comp_assoc, comp_assoc, hji, comp_idMap]
end

section
set_option linter.unusedVariables false

theorem theorem_69.{u_4} : ∀
  (T :
    @DomainTheory.NeighbourhoodSystems.Endofunctor.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}),
  DomainTheory.NeighbourhoodSystems.ContinuousOnMaps.{u_4} T →
    ∀ {D : DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}}
      (iso :
        @DomainTheory.NeighbourhoodSystems.Iso.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
            DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
          D)
      (B :
        @DomainTheory.NeighbourhoodSystems.TAlgebra.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
          DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T),
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{u_4, u_4}
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B)).carrier
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).carrier
          (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B)).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
              DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.str.{u_4 + 1, u_4}
            DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
            DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B) →
        Nonempty.{u_4 + 1}
          (@Subtype.{u_4 + 1}
            (@DomainTheory.NeighbourhoodSystems.AlgHom.{u_4 + 1, u_4} DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
              DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                  (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                  D iso))
              B)
            fun
              (g :
                @DomainTheory.NeighbourhoodSystems.AlgHom.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))
                  B) =>
            @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict.{u_4, u_4}
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).carrier
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                  (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                    (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                      (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                        DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                        DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                      D iso))).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T B).sys
              (@DomainTheory.NeighbourhoodSystems.AlgHom.hom.{u_4 + 1, u_4}
                DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T
                (@DomainTheory.NeighbourhoodSystems.TAlgebra.mk.{u_4 + 1, u_4}
                  DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                  DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D
                  (@DomainTheory.NeighbourhoodSystems.Iso.hom.{u_4 + 1, u_4}
                    DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                    DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4}
                    (@DomainTheory.NeighbourhoodSystems.Endofunctor.obj.{u_4 + 1, u_4}
                      DomainTheory.NeighbourhoodSystems.DomainObj.{u_4}
                      DomainTheory.NeighbourhoodSystems.instCategoryDomainObj.{u_4} T D)
                    D iso))
                B g)) :=
  DomainTheory.NeighbourhoodSystems.nonempty_algHom_of_continuousOnMaps.{u_4}
end

end DomainTheory.NeighbourhoodSystems
end

section
-- StrictDomainObj.lean
universe w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- An object of Scott's category (Exercise 6.19): a token type, a neighbourhood system on it, and the
standing assumption `∅ ∉ 𝒟` (every neighbourhood is non-empty). -/
structure StrictDomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system. -/
  sys : NeighborhoodSystem carrier
  /-- Scott's standing assumption `∅ ∉ 𝒟`. -/
  nonempty : ∀ X, sys.mem X → X.Nonempty

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- **The category of `∅`-free domains and strict maps.** Morphisms are strict approximable maps
(`StrictMap`, Exercise 5.10); identities and associative composition come from Theorem 2.5, and
strictness is preserved by `isStrict_idMap` / `isStrict_comp`. -/
instance : Category StrictDomainObj where
  Hom D E := StrictMap D.sys E.sys
  id D := ⟨ApproximableMap.idMap D.sys, isStrict_idMap⟩
  comp f g := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (ApproximableMap.comp_idMap f.1)
  comp_id f := Subtype.ext (ApproximableMap.idMap_comp f.1)
  assoc f g h := Subtype.ext (ApproximableMap.comp_assoc h.1 g.1 f.1).symm
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem StrictDomainObj.id_val (D : StrictDomainObj) :
    ((𝟙 D) : StrictMap D.sys D.sys).1 = ApproximableMap.idMap D.sys := rfl
end

section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

@[simp] theorem StrictDomainObj.comp_val {D E F : StrictDomainObj}
    (g : (E ⟶ F)) (f : (D ⟶ E)) :
    ((g ⊚ f : StrictMap D.sys F.sys)).1 = g.1.comp f.1 := rfl
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embZero {X : Set α} {p : List Bool} {a : α} :
    (p, a) ∈ embZero X ↔ p = [] ∧ a ∈ X := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embL {P : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embL P ↔ ∃ p', p = true :: p' ∧ (p', a) ∈ P := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embR {Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embR Q ↔ ∃ q', p = false :: q' ∧ (q', a) ∈ Q := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_embPair {P Q : Set (List Bool × α)} {p : List Bool} {a : α} :
    (p, a) ∈ embPair P Q ↔
      (∃ p', p = true :: p' ∧ (p', a) ∈ P) ∨ (∃ q', p = false :: q' ∧ (q', a) ∈ Q) := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem mem_Gamma {D : NeighborhoodSystem α} {p : List Bool} {a : α} :
    (p, a) ∈ Gamma D ↔ a ∈ D.master := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem Gamma_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    (Gamma D).Nonempty := by
  obtain ⟨a, ha⟩ := hD D.master D.master_mem; exact ⟨([], a), ha⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_inter (P Q P' Q' : Set (List Bool × α)) :
    embPair P Q ∩ embPair P' Q' = embPair (P ∩ P') (Q ∩ Q') := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embPair]
  rcases p with _ | ⟨b, ps⟩
  · simp
  · cases b <;> simp [List.cons.injEq]

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_nonempty {P Q : Set (List Bool × α)} (hP : P.Nonempty) :
    (embPair P Q).Nonempty := by
  obtain ⟨⟨p', a⟩, hP⟩ := hP; exact ⟨(true :: p', a), Or.inl ⟨p', rfl, hP⟩⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_subset {P Q P' Q' : Set (List Bool × α)} :
    embPair P Q ⊆ embPair P' Q' ↔ P ⊆ P' ∧ Q ⊆ Q' := by
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨p', a⟩ := t
      have hmem : ((true :: p', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inl ⟨p', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', hP'⟩ | ⟨q'', hq'', -⟩
      · simp only [List.cons.injEq, true_and] at hp''; exact hp'' ▸ hP'
      · exact absurd hq'' (by simp)
    · obtain ⟨q', a⟩ := t
      have hmem : ((false :: q', a) : List Bool × α) ∈ embPair P' Q' :=
        h (Or.inr ⟨q', rfl, ht⟩)
      rcases hmem with ⟨p'', hp'', -⟩ | ⟨q'', hq'', hQ'⟩
      · exact absurd hp'' (by simp)
      · simp only [List.cons.injEq, true_and] at hq''; exact hq'' ▸ hQ'
  · rintro ⟨hP, hQ⟩ t ht
    rcases ht with ⟨p', hp', hPmem⟩ | ⟨q', hq', hQmem⟩
    · exact Or.inl ⟨p', hp', hP hPmem⟩
    · exact Or.inr ⟨q', hq', hQ hQmem⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_injective {P Q P' Q' : Set (List Bool × α)}
    (h : embPair P Q = embPair P' Q') : P = P' ∧ Q = Q' := by
  obtain ⟨hP, hQ⟩ := embPair_subset.mp h.subset
  obtain ⟨hP', hQ'⟩ := embPair_subset.mp h.symm.subset
  exact ⟨Set.Subset.antisymm hP hP', Set.Subset.antisymm hQ hQ'⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embPair_subset_Gamma {D : NeighborhoodSystem α} {P Q : Set (List Bool × α)}
    (hP : P ⊆ Gamma D) (hQ : Q ⊆ Gamma D) : embPair P Q ⊆ Gamma D := by
  rintro ⟨p, a⟩ (⟨p', -, hPmem⟩ | ⟨q', -, hQmem⟩)
  · have h := hP hPmem; exact h
  · have h := hQ hQmem; exact h

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_inter (X X' : Set α) :
    embZero X ∩ embZero X' = embZero (X ∩ X' : Set α) := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero]
  tauto

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_inter_embPair (X : Set α) (P Q : Set (List Bool × α)) :
    embZero X ∩ embPair P Q = ∅ := by
  ext ⟨p, a⟩
  simp only [Set.mem_inter_iff, mem_embZero, mem_embPair, Set.mem_empty_iff_false, iff_false,
    not_and, not_or]
  rintro ⟨rfl, -⟩
  exact ⟨by rintro ⟨p', hp', -⟩; exact absurd hp' (by simp), by rintro ⟨q', hq', -⟩; exact absurd hq' (by simp)⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_nonempty {X : Set α} (hX : X.Nonempty) : (embZero X).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨([], a), rfl, ha⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_subset {X X' : Set α} : embZero X ⊆ embZero X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha
    have : (([], a) : List Bool × α) ∈ embZero X' := h ⟨rfl, ha⟩
    exact this.2
  · intro h t ht; exact ⟨ht.1, h ht.2⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_injective {X X' : Set α} (h : embZero X = embZero X') : X = X' :=
  Set.Subset.antisymm (embZero_subset.mp h.subset) (embZero_subset.mp h.symm.subset)

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem embZero_subset_Gamma {D : NeighborhoodSystem α} {X : Set α} (hX : D.mem X) :
    embZero X ⊆ Gamma D := by
  rintro ⟨p, a⟩ ⟨-, ha⟩; exact D.sub_master hX ha

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- Under Scott's standing assumption `∅ ∉ 𝒟`, no neighbourhood of `D^§` is empty. -/
theorem memS_nonempty {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {W : Set (List Bool × α)} (hW : MemS D W) : W.Nonempty := by
  induction hW with
  | gamma => exact Gamma_nonempty hD
  | zero hX => exact embZero_nonempty (hD _ hX)
  | pair _ _ ihP _ => exact embPair_nonempty ihP

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- Every neighbourhood of `D^§` is a subset of the master `Γ` (Scott's `𝒟^§ ⊆ 𝒫(Γ)`). -/
theorem memS_subset_gamma {D : NeighborhoodSystem α} {W : Set (List Bool × α)}
    (hW : MemS D W) : W ⊆ Gamma D := by
  induction hW with
  | gamma => exact subset_rfl
  | zero hX => exact embZero_subset_Gamma hX
  | pair _ _ ihP ihQ => exact embPair_subset_Gamma ihP ihQ

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 — closure under consistent intersection.** Scott's central verification, "by
induction on the number of steps required to put `X` and `Y` into `𝒟^§`". The cross cases
(`0A ∩ (1P∪2Q) = ∅`, etc.) are discharged because the consistency witness `Z` is non-empty
(`memS_nonempty`); the `0A ∩ 0B` case uses `𝒟`'s own closure; the `(1P∪2Q) ∩ (1P'∪2Q')` case recurses
on `P, P'` and `Q, Q'`. -/
theorem memS_inter {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) :
    ∀ {X : Set (List Bool × α)}, MemS D X → ∀ {Y : Set (List Bool × α)}, MemS D Y →
      ∀ {Z : Set (List Bool × α)}, MemS D Z → Z ⊆ X ∩ Y → MemS D (X ∩ Y) := by
  intro X hX
  induction hX with
  | gamma =>
    intro Y hY Z _ _
    rw [Set.inter_eq_right.mpr (memS_subset_gamma hY)]; exact hY
  | @zero A hA =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hA)]; exact MemS.zero hA
    | @zero B hB =>
      rw [embZero_inter]
      -- the witness `Z` must be a `0C`; read off `C ⊆ A ∩ B`, then `D`'s closure gives `A ∩ B ∈ 𝒟`.
      rw [embZero_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        exact MemS.zero (D.inter_mem hA hB hC (embZero_subset.mp hsub))
      | @pair P Q hP hQ =>
        obtain ⟨t, hmem⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hempty : t.1 = [] := (hsub hmem).1
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · rw [hp'] at hempty; exact absurd hempty (by simp)
        · rw [hq'] at hempty; exact absurd hempty (by simp)
    | @pair P Q _ _ =>
      rw [embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
  | @pair P Q hP hQ ihP ihQ =>
    intro Y hY Z hZ hsub
    cases hY with
    | gamma =>
      rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))]
      exact MemS.pair hP hQ
    | @zero B hB =>
      rw [Set.inter_comm, embZero_inter_embPair] at hsub
      obtain ⟨z, hz⟩ := memS_nonempty hD hZ
      exact absurd (hsub hz) (Set.notMem_empty z)
    | @pair P' Q' hP' hQ' =>
      rw [embPair_inter]
      rw [embPair_inter] at hsub
      cases hZ with
      | gamma =>
        obtain ⟨a, ha⟩ := hD D.master D.master_mem
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ Gamma D from ha)) (by simp)
      | @zero C hC =>
        obtain ⟨a, ha⟩ := hD C hC
        exact absurd (hsub (show (([], a) : List Bool × α) ∈ embZero C from ⟨rfl, ha⟩)) (by simp)
      | @pair Z₀ Z₁ hZ₀ hZ₁ =>
        obtain ⟨hsub₀, hsub₁⟩ := embPair_subset.mp hsub
        exact MemS.pair (ihP hP' hZ₀ hsub₀) (ihQ hQ' hZ₁ hsub₁)

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 (Scott 1981, PRG-19).** The *tree algebra* `D^§`: a neighbourhood system over
`Γ = {1,2}* 0 Δ`, under the standing assumption `∅ ∉ 𝒟` (`hD`). -/
abbrev Dsharp (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem (List Bool × α) where
  mem := MemS D
  master := Gamma D
  master_nonempty := by
    obtain ⟨a, ha⟩ := D.master_nonempty
    exact ⟨([], a), ha⟩
  master_mem := MemS.gamma
  inter_mem := fun hX hY hZ hsub => memS_inter hD hX hY hZ hsub
  sub_master := memS_subset_gamma

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem Dsharp_mem {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty}
    {W : Set (List Bool × α)} : (Dsharp D hD).mem W ↔ MemS D W := Iff.rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

@[simp] theorem Dsharp_master {D : NeighborhoodSystem α} {hD : ∀ X, D.mem X → X.Nonempty} :
    (Dsharp D hD).master = Gamma D := rfl

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem memS_embPair_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
    {P Q : Set (List Bool × α)} (h : MemS D (embPair P Q)) : MemS D P ∧ MemS D Q := by
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : (([], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1
    rcases h1 with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · simp at hp'
    · simp at hq'
  | @zero X hX =>
    exfalso
    obtain ⟨t, ht⟩ := embZero_nonempty (hD X hX)
    have hempty : t.1 = [] := ht.1
    rw [← hW] at ht
    rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
    · rw [hp'] at hempty; simp at hempty
    · rw [hq'] at hempty; simp at hempty
  | @pair P' Q' hP' hQ' =>
    obtain ⟨hPP, hQQ⟩ := embPair_injective hW
    rw [hPP, hQQ]; exact ⟨hP', hQ'⟩

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem memS_embZero_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α}
    (h : MemS D (embZero X)) : D.mem X := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1; exact absurd h1.1 (by simp)
  | @zero X' hX' => rw [embZero_injective hW]; exact hX'
  | @pair P Q hP hQ =>
    exfalso
    obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
    have hcons : t.1 ≠ [] := by
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp [hp']
      · simp [hq']
    have hz : t ∈ embZero X := by rw [← hW] at ht; exact ht
    exact hcons hz.1

end Example61
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- No neighbourhood of `D^§ × D^§` is empty (needed to form the sum `D + (D^§ × D^§)`). -/
theorem prod_dsharp_nonempty :
    ∀ V, (prod (Dsharp D hD) (Dsharp D hD)).mem V → V.Nonempty := by
  rintro V ⟨P, Q, hP, hQ, rfl⟩
  obtain ⟨t, ht⟩ := memS_nonempty hD hP
  exact ⟨Sum.inl t, mem_prodNbhd_inl.mpr ht⟩

end Equation

end Example61
end

end DomainTheory.NeighbourhoodSystems
end

section
-- Definition613/MonotoneAt.lean
universe w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- **Definition 6.13, monotone part (pointwise).** Given a subdomain relation `h : D ◁ E`, the data
witnessing that the functor `T` carries it to `T(D) ◁ T(E)` *and* carries the projection pair `i, j`
of 6.12 to the projection pair of `T(D) ◁ T(E)`.

Because `T` may change the token type, the two image systems live a priori over different carriers;
`carrier_eq` records that they coincide, `sub` is the resulting subdomain relation (with `T(E)`'s
system transported into `T(D)`'s carrier), and `inj_heq`/`proj_heq` say the canonical 6.12 maps of
`sub` are `T(i)` and `T(j)` (up to that transport, hence `HEq`). -/
structure MonotoneAt (T : Endofunctor DomainObj.{w}) {α : Type w}
    {D E : NeighborhoodSystem α} (h : D ◁ E) : Prop where
  /-- The two image carriers coincide, so `T(D) ◁ T(E)` can be stated. -/
  carrier_eq : (T.obj ⟨α, E⟩).carrier = (T.obj ⟨α, D⟩).carrier
  /-- The image subdomain relation `T(D) ◁ T(E)` (with `T(E)`'s system carried into `T(D)`'s
  carrier). -/
  sub : (T.obj ⟨α, D⟩).sys ◁
    (carrier_eq ▸ (T.obj ⟨α, E⟩).sys : NeighborhoodSystem (T.obj ⟨α, D⟩).carrier)
  /-- The injection of `T(D) ◁ T(E)` is `T(i)` (Scott: the pair is mapped to `T(i), T(j)`). -/
  inj_heq : HEq (T.map (X := ⟨α, D⟩) (Y := ⟨α, E⟩) h.inj) sub.inj
  /-- The projection of `T(D) ◁ T(E)` is `T(j)`. -/
  proj_heq : HEq (T.map (X := ⟨α, E⟩) (Y := ⟨α, D⟩) h.proj) sub.proj

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
universe w

end
end DomainTheory.NeighbourhoodSystems
end
