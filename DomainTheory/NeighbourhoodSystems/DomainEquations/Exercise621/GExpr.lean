/-ai
The extended functor-expression algebra has six constructors: a constant Scott system, the identity variable, and binary separated sum, separated product, coalesced sum, and smash product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}
variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}
variable {A₀ A₁ B₀ B₁ : ScottSys}
variable {C₀ C₁ : ScottSys}

/-- **The extended functor-expression algebra** (constants, identity, `+`, `×`, `⊕`, `⊗`). -/
inductive GExpr where
  | const : ScottSys → GExpr
  | var : GExpr
  | sum : GExpr → GExpr → GExpr
  | prod : GExpr → GExpr → GExpr
  | oplus : GExpr → GExpr → GExpr
  | otimes : GExpr → GExpr → GExpr

end Exercise619
end DomainTheory.NeighbourhoodSystems
