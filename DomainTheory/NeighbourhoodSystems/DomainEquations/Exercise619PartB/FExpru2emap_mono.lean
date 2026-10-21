/-ai
The action of a construct on maps is monotone: a sharper approximable map is sent to a sharper image.

The proof is by induction on the construct. A constant image is unchanged. The identity variable is the given inequality. A sum applies the monotonicity lemma for the sum action to the two inductive inequalities. A product applies the monotonicity lemma for the product action.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumMapTok_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodMapTok_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619


variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}


/-- **`λf. T(f)` is monotone.** A sharper map `f ≤ f'` is sent to a sharper image `T(f) ≤ T(f')` —
the monotonicity half of *continuous on maps*. -/
theorem FExpr.map_mono : (T : FExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum T₀ T₁, _, _, _, _, h => sumMapTok_mono (T₀.map_mono h) (T₁.map_mono h)
  | .prod T₀ T₁, _, _, _, _, h => prodMapTok_mono (T₀.map_mono h) (T₁.map_mono h)

end Exercise619
end DomainTheory.NeighbourhoodSystems
