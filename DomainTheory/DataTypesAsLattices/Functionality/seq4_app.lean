module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_body_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_app (a b c d z : Pomega) :
    funOf (seq4 a b c d) z =
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))) :=
  beta (seq4_body_isScottContinuous a b c d) z

end DomainTheory.DataTypesAsLattices
