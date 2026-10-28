module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510
section

def ContinuousOnMaps (T : Endofunctor DomainObj) : Prop :=
  ∀ D E : DomainObj,
    ∃ Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys),
      ∀ f : StrictMap D.sys E.sys,
        (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1
end

section

theorem ContinuousOnMaps.isStrict_map {T : Endofunctor DomainObj} (h : ContinuousOnMaps T)
    {D E : DomainObj} (f : StrictMap D.sys E.sys) :
    IsStrict (T.map (X := D) (Y := E) f.1) := by
  obtain ⟨Φ, hΦ⟩ := h D E
  rw [← hΦ f]
  exact (toStrictMap (Φ.toElementMap (toStrictFilter f))).2
end

section

theorem toStrictMap_toStrictFilter {α β : Type*} {V₀ : NeighborhoodSystem α}
    {V₁ : NeighborhoodSystem β} (f : StrictMap V₀ V₁) :
    toStrictMap (toStrictFilter f) = f :=
  (strictFunEquiv V₀ V₁).right_inv f
end

section

theorem continuousOnMaps_id : ContinuousOnMaps (idEndofunctor DomainObj) := by
  intro D E
  refine ⟨idMap (strictFun D.sys E.sys), fun f => ?_⟩
  show (toStrictMap ((idMap (strictFun D.sys E.sys)).toElementMap (toStrictFilter f))).1 = f.1
  rw [toElementMap_idMap, toStrictMap_toStrictFilter]
end

section
universe u
variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

theorem comp_desc_eq_id (hA : IsInitial A) (hB : IsInitial B) :
    (hB.desc A).comp (hA.desc B) = AlgHom.id A := by
  rw [hA.uniq A ((hB.desc A).comp (hA.desc B)), hA.uniq A (AlgHom.id A)]

end
end DomainTheory.NeighbourhoodSystems
end
