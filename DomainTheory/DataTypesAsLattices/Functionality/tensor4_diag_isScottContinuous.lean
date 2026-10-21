/-ai
The diagonal map sending z to the four-fold tensor of z with itself is Scott continuous.

Continuity of the graph in the parameter reduces to continuity of the body at each fixed u. There the four-way sequence of four continuous maps is continuous, and each map is left application at the corresponding component of u.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_comp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensor4_diag_isScottContinuous :
    IsScottContinuous (fun z => tensor4 z z z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      seq4 (funOf z (funOf u (ofNat 0)))
        (funOf z (funOf u (ofNat 1)))
        (funOf z (funOf u (ofNat 2)))
        (funOf z (funOf u (ofNat 3))))
    (fun u =>
      seq4_comp_isScottContinuous
        (funOf_isScottContinuous_left (funOf u (ofNat 0)))
        (funOf_isScottContinuous_left (funOf u (ofNat 1)))
        (funOf_isScottContinuous_left (funOf u (ofNat 2)))
        (funOf_isScottContinuous_left (funOf u (ofNat 3))))

end DomainTheory.DataTypesAsLattices
