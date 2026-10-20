module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_id

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}











/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** Every construct `T` preserves identities. -/
theorem FExpr.map_id : (T : FExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const D, _ => rfl
  | .var, _ => rfl
  | .sum T₀ T₁, X => by
      show sumMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).sum (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, sumMapTok_id]
  | .prod T₀ T₁, X => by
      show prodMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).prod (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, prodMapTok_id]

end Exercise619
end DomainTheory.NeighbourhoodSystems
