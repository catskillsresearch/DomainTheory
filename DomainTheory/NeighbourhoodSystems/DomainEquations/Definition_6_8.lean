module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.continuousOnMaps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.SmashProduct

/-- Scott's Definition 6.8: a functor is continuous on strict function spaces. -/
theorem definition_68 (T : Endofunctor DomainObj) :
    ContinuousOnMaps T ↔
      ∀ D E : DomainObj,
        ∃ Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys),
          ∀ f : StrictMap D.sys E.sys,
            (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1 :=
  Iff.rfl

end DomainTheory.NeighbourhoodSystems
