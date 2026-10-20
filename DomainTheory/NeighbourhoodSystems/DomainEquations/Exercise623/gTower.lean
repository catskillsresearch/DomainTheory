module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

/-- **The tower `Tⁿ({Γ})`** of `∅`-free systems over `Str`: `T⁰({Γ}) = {Γ}`, `Tⁿ⁺¹({Γ}) =
T(Tⁿ({Γ}))`. -/
def gTower (T : GExpr) : ℕ → ScottSys
  | 0 => gGen T
  | n + 1 => T.obj (gTower T n)

end Exercise619

end DomainTheory.NeighbourhoodSystems
