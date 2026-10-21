/-ai
The right-nested n-ary fold of a binary expression constructor, applied to a head and a list, returns the head when the list is empty and otherwise applies the constructor to the head and the fold of the tail. Instantiated at separated sum, separated product, coalesced sum, or smash product, this is the corresponding n-ary operation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr

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

/-- **Right-nested n-ary fold** of a binary construct-operation `op` over a non-empty list `a, l…`.
With `op = .sum`/`.prod`/`.oplus`/`.otimes` this is the n-ary `+`/`×`/`⊕`/`⊗`. -/
def GExpr.naryOp (op : GExpr → GExpr → GExpr) (a : GExpr) : List GExpr → GExpr
  | [] => a
  | b :: l => op a (GExpr.naryOp op b l)

end Exercise619

end DomainTheory.NeighbourhoodSystems
