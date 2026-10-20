module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimes

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

variable {A₀ A₁ B₀ B₁ : ScottSys}

variable {C₀ C₁ : ScottSys}

/-- **The action of `T` on objects.** -/
def GExpr.obj : GExpr → ScottSys → ScottSys
  | .const D, _ => D
  | .var, X => X
  | .sum a b, X => (a.obj X).sum (b.obj X)
  | .prod a b, X => (a.obj X).prod (b.obj X)
  | .oplus a b, X => (a.obj X).oplus (b.obj X)
  | .otimes a b, X => (a.obj X).otimes (b.obj X)

end Exercise619

end DomainTheory.NeighbourhoodSystems
