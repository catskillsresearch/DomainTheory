
module

public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tagInj_isScottContinuous (i : ℕ) :
    IsScottContinuous (tagInj i) :=
  pairSeq_isScottContinuous_right (ofNat i)

end DomainTheory.DataTypesAsLattices
