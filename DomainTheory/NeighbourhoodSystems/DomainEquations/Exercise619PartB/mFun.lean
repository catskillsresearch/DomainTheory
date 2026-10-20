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

/-- **The token-level master recursion.** `mFun T Γ` computes `tok(T({Γ}))` purely from `Γ`, without
touching the neighbourhood data of `{Γ}` (`mFun_eq_master`): constants are constant, the identity
returns `Γ`, and both sum and product wrap the two component token sets with the tags `0,1` under a
common root `Λ` (`sumTokMaster = prodTokNbhd` agree on masters). -/
def mFun : FExpr → Set Str → Set Str
  | .const C, _ => C.sys.master
  | .var, Γ => Γ
  | .sum T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))
  | .prod T₀ T₁, Γ => insert ([] : Str) (embBit false (mFun T₀ Γ) ∪ embBit true (mFun T₁ Γ))

end Exercise619

end DomainTheory.NeighbourhoodSystems
