module

public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def omegaComb (u : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf x x))

namespace omegaComb

theorem app (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) :=
  beta (theorem_1_3 (funOf.isScottContinuous u) diagApp_isScottContinuous) x

theorem isScottContinuous : IsScottContinuous omegaComb :=
  graph_const_isScottContinuous
    (fun u x => funOf u (funOf x x))
    (fun x => funOf.isScottContinuous_left (funOf x x))

end omegaComb

end DomainTheory.DataTypesAsLattices
