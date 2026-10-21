/-ai
The action of a functor expression on Scott systems sends a constant to that constant, the identity expression to the system itself, a sum to the sum of the two component systems, and a product to the product of the two component systems.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.ScottSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prod

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- **The action of `T` on objects.** -/
def FExpr.obj : FExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum T₀ T₁, X => (T₀.obj X).sum (T₁.obj X)
  | .prod T₀ T₁, X => (T₀.obj X).prod (T₁.obj X)

end Exercise619

end DomainTheory.NeighbourhoodSystems
