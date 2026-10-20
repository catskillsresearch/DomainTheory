module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.toStrictMap_toStrictFilter

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u





/-- **The identity functor is continuous on maps** — the basic witness that Definition 6.8 is
satisfiable. The representing approximable map is the identity on `(D →⊥ E)`. -/
theorem continuousOnMaps_id : ContinuousOnMaps (idEndofunctor DomainObj) := by
  intro D E
  refine ⟨idMap (strictFun D.sys E.sys), fun f => ?_⟩
  show (toStrictMap ((idMap (strictFun D.sys E.sys)).toElementMap (toStrictFilter f))).1 = f.1
  rw [toElementMap_idMap, toStrictMap_toStrictFilter]

end DomainTheory.NeighbourhoodSystems
