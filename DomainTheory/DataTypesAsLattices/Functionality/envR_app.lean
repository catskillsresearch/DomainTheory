module

public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.envR
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.envR_map_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem envR_app (t : Pomega) :
    funOf envR t = graph (fun n => funOf lambR (funOf t n)) :=
  beta envR_map_isScottContinuous t

end DomainTheory.DataTypesAsLattices
