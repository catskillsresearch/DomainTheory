/-ai
Application of the four-way sequence of a, b, c, and d to z is the nested conditional that tests z, its predecessor, the predecessor of that predecessor, and the threefold predecessor, returning a, b, c, d, and finally bottom.

This is the beta law for the graph of that body, using Scott continuity of the body.
ai-/

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
