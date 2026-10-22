module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Kcomb_app (x : Pomega) :
    funOf Kcomb x = graph (fun _ => x) :=
  beta (graph_const_isScottContinuous (fun x _ => x)
    (fun _ => id_isScottContinuous)) x

end DomainTheory.DataTypesAsLattices
