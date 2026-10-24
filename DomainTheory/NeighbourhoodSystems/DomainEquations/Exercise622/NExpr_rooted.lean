module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cnat
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.MExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NStarExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.nil_mem_Cnat

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


theorem NExpr_rooted : NExpr.RootedConst := ⟨nil_mem_Cnat, trivial⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
