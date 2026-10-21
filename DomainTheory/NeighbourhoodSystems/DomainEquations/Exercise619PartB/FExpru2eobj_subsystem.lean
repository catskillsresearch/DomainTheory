/-ai
The action of a construct on objects is monotone for the subsystem relation: if one Scott system is a subsystem of another, then the image of the first is a subsystem of the image of the second.

The proof is by induction on the construct. A constant is a subsystem of itself. The identity variable is the given relation. A sum applies the subsystem lemma for the token sum to the two inductive relations. A product applies the subsystem lemma for the token product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sumTok_subsystem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodTok_subsystem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}













/-- **`λX. T(X)` is monotone on domains.** Whenever `X ◁ Y` we have `T(X) ◁ T(Y)`. -/
theorem FExpr.obj_subsystem : (T : FExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum T₀ T₁, _, _, h => sumTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)
  | .prod T₀ T₁, _, _, h => prodTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)

end Exercise619
end DomainTheory.NeighbourhoodSystems
