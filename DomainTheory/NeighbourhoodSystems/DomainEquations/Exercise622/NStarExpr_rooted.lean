module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619








theorem NStarExpr_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) :
    (NStarExpr N).RootedConst := ⟨hN, hN, trivial⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
