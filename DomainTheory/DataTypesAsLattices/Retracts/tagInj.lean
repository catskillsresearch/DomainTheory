module

public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.PairSeq
public import DomainTheory.DataTypesAsLattices.Graph.funOf
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def tagInj (i : ℕ) (x : Pomega) : Pomega := pairSeq (ofNat i) x

namespace tagInj

theorem isScottContinuous (i : ℕ) :
    IsScottContinuous (tagInj i) :=
  PairSeq.isScottContinuous_right (ofNat i)

theorem one (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 1) = x :=
  PairSeq.app_one (ofNat i) x

theorem zero (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 0) = ofNat i :=
  PairSeq.app_zero (ofNat i) x

end tagInj

end DomainTheory.DataTypesAsLattices
