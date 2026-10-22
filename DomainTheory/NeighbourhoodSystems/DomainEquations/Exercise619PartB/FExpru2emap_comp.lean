module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_comp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_comp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **Functor law 2 — `T(g ∘ f) = T(g) ∘ T(f)`.** Every construct `T` preserves composition; together
with `map_id` this shows *these are all functors*. -/
theorem FExpr.map_comp : (T : FExpr) → {X Y Z : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    (g : ApproximableMap Y.sys Z.sys) → T.map (g.comp f) = (T.map g).comp (T.map f)
  | .const D, _, _, _, _, _ => (idMap_comp (idMap D.sys)).symm
  | .var, _, _, _, _, _ => rfl
  | .sum T₀ T₁, _, _, _, f, g => by
      show sumMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (sumMapTok (T₀.map g) (T₁.map g)).comp (sumMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, sumMapTok_comp]
  | .prod T₀ T₁, _, _, _, f, g => by
      show prodMapTok (T₀.map (g.comp f)) (T₁.map (g.comp f))
          = (prodMapTok (T₀.map g) (T₁.map g)).comp (prodMapTok (T₀.map f) (T₁.map f))
      rw [T₀.map_comp f g, T₁.map_comp f g, prodMapTok_comp]

end Exercise619
end DomainTheory.NeighbourhoodSystems
