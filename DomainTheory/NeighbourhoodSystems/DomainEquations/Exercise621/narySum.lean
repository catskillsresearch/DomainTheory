module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.naryOp

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

/-- n-ary separated sum `T₀ + T₁ + ⋯ + Tₙ`. -/
def GExpr.narySum : GExpr → List GExpr → GExpr := GExpr.naryOp GExpr.sum

end Exercise619

end DomainTheory.NeighbourhoodSystems
