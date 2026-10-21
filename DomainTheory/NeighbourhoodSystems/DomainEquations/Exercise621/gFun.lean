/-ai
The token-level master recursion of an expression sends a constant to its master and the variable to the argument set. Each of the four binary constructors inserts the empty string into the union of the false-tagged and true-tagged recursive values, so all four share one tagged-union body.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimes

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

/-- **The token-level master recursion for `GExpr`.** All four binary operations share the same body
(`sumTokMaster = prodTokNbhd` on masters). -/
def gFun : GExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .prod a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .oplus a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))
  | .otimes a b, Γ => insert ([] : Str) (embBit false (gFun a Γ) ∪ embBit true (gFun b Γ))

end Exercise619

end DomainTheory.NeighbourhoodSystems
