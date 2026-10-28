module

public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Kcomb_app (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  beta (graph_const_isScottContinuous (fun x _ => x)
    (fun _ => id_isScottContinuous)) x

end DomainTheory.DataTypesAsLattices
