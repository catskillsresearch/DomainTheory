module

public import DomainTheory.DataTypesAsLattices.Retracts.curryC
public import DomainTheory.DataTypesAsLattices.Retracts.diagC
public import DomainTheory.DataTypesAsLattices.Retracts.evalC
public import DomainTheory.DataTypesAsLattices.Retracts.fstC
public import DomainTheory.DataTypesAsLattices.Retracts.sndC

import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Graph.beta
import DomainTheory.DataTypesAsLattices.Enumeration.ContinuityHelpers
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def whichC : Pomega := fstC

namespace whichC

theorem app (u : Pomega) : funOf whichC u = funOf u (ofNat 0) :=
  fstC.app u

end whichC

def outC : Pomega := sndC

def outleftC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem)

namespace outleftC

theorem isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem) :=
  ContinuityHelpers.tuple
    (fun y => condSet.isScottContinuous_left y botElem)
    (fun tes => condSet.isScottContinuous_mid tes botElem)
    (funOf.isScottContinuous_left (ofNat 0))
    (funOf.isScottContinuous_left (ofNat 1))

theorem app (u : Pomega) :
    funOf outleftC u = condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem :=
  beta outleftC.isScottContinuous u

end outleftC

def outrightC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)))

namespace outrightC

theorem isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1))) :=
  ContinuityHelpers.tuple
    (fun y => condSet.isScottContinuous_left botElem y)
    (fun tes => condSet.isScottContinuous_right tes botElem)
    (funOf.isScottContinuous_left (ofNat 0))
    (funOf.isScottContinuous_left (ofNat 1))

theorem app (u : Pomega) :
    funOf outrightC u = condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)) :=
  beta outrightC.isScottContinuous u

end outrightC

def inrightC : Pomega := graph (fun x => pairSeq (ofNat 1) x)

theorem inrightC_app (x : Pomega) :
    funOf inrightC x = pairSeq (ofNat 1) x :=
  beta (PairSeq.isScottContinuous_right (ofNat 1)) x

def inleftC : Pomega := graph (fun x => pairSeq (ofNat 0) x)

namespace inleftC

theorem app (x : Pomega) :
    funOf inleftC x = pairSeq (ofNat 0) x :=
  beta (PairSeq.isScottContinuous_right (ofNat 0)) x

end inleftC

theorem curryC_isScottContinuous :
    IsScottContinuous (fun u =>
      graph (fun x => graph (fun y => funOf u (pairSeq x y)))) :=
  graph_const_isScottContinuous
    (fun u x => graph (fun y => funOf u (pairSeq x y)))
    (fun x =>
      graph_const_isScottContinuous
        (fun u y => funOf u (pairSeq x y))
        (fun y => funOf.isScottContinuous_left (pairSeq x y)))

theorem curryC_app (u : Pomega) :
    funOf curryC u = graph (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  beta curryC_isScottContinuous u

theorem curry_mid_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  graph_const_isScottContinuous
    (fun x y => funOf u (pairSeq x y))
    (fun y => theorem_1_3 (funOf.isScottContinuous u)
      (PairSeq.isScottContinuous_left y))

theorem diagC_app (u : Pomega) : funOf diagC u = pairSeq u u :=
  beta (ContinuityHelpers.on_diag
    PairSeq.isScottContinuous_left PairSeq.isScottContinuous_right) u

theorem evalC_isScottContinuous :
    IsScottContinuous (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1))) :=
  ContinuityHelpers.tuple
    (fun y => funOf.isScottContinuous_left y)
    (fun t => funOf.isScottContinuous t)
    (funOf.isScottContinuous_left (ofNat 0))
    (funOf.isScottContinuous_left (ofNat 1))

theorem evalC_app (u : Pomega) :
    funOf evalC u = funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)) :=
  beta evalC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
