/-ai
The identity endofunctor is continuous on maps.

The witnessing approximable map is the identity of the strict function space. The action of the identity on elements is the identity, and converting a strict map to a filter and back returns the original strict map, so the underlying map is the original one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.toStrictMap_toStrictFilter

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


/-- **The identity functor is continuous on maps** — the basic witness that Definition 6.8 is
satisfiable. The representing approximable map is the identity on `(D →⊥ E)`. -/
theorem continuousOnMaps_id : ContinuousOnMaps (idEndofunctor DomainObj) := by
  intro D E
  refine ⟨idMap (strictFun D.sys E.sys), fun f => ?_⟩
  show (toStrictMap ((idMap (strictFun D.sys E.sys)).toElementMap (toStrictFilter f))).1 = f.1
  rw [toElementMap_idMap, toStrictMap_toStrictFilter]

end DomainTheory.NeighbourhoodSystems
