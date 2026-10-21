/-ai
The vertical-naturals expression is rooted.

Rootedness of a coalesced sum is the conjunction of rootedness of its arguments. The constant two-point domain contributes membership of the empty string in its master, and the variable is rooted outright.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.nil_mem_Cnat

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


theorem NExpr_rooted : NExpr.RootedConst := ⟨nil_mem_Cnat, trivial⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
