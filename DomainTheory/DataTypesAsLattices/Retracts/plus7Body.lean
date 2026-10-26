module

public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Body of the seven-way tagged sum of (4.44). -/
def plus7Body (a0 a1 a2 a3 a4 a5 a6 u : Pomega) : Pomega :=
  dcondSet (funOf u (ofNat 0)) (tagInj 0 (funOf a0 (funOf u (ofNat 1))))
    (dcondSet (predSet (funOf u (ofNat 0))) (tagInj 1 (funOf a1 (funOf u (ofNat 1))))
      (dcondSet (predSet (predSet (funOf u (ofNat 0))))
        (tagInj 2 (funOf a2 (funOf u (ofNat 1))))
        (dcondSet (predSet^[3] (funOf u (ofNat 0)))
          (tagInj 3 (funOf a3 (funOf u (ofNat 1))))
          (dcondSet (predSet^[4] (funOf u (ofNat 0)))
            (tagInj 4 (funOf a4 (funOf u (ofNat 1))))
            (dcondSet (predSet^[5] (funOf u (ofNat 0)))
              (tagInj 5 (funOf a5 (funOf u (ofNat 1))))
              (dcondSet (predSet^[6] (funOf u (ofNat 0)))
                (tagInj 6 (funOf a6 (funOf u (ofNat 1))))
                topElem))))))

end DomainTheory.DataTypesAsLattices
