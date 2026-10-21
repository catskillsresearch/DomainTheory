/-ai
The Kleene iteration of the token-level master recursion starts at the singleton of the empty word and applies the recursion at each successor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.ScottSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.FExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.mFun

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}

/-- The **Kleene iteration** `mFunⁿ({Λ})` whose union is the least fixed point above `{Λ}`. -/
def mIter (T : FExpr) : ℕ → Set Str
  | 0 => {([] : Str)}
  | n + 1 => mFun T (mIter T n)

end Exercise619

end DomainTheory.NeighbourhoodSystems
