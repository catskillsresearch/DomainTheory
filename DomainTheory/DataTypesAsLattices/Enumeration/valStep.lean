module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.minExtend_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.valStepValue
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.minExtend

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.7).** One step of the enumerator.  The positive
branch is written as `minExtend`; this is extensionally Scott's existential
clause and exposes its continuity. -/
def valStep (v : Pomega) : Pomega :=
  graph (fun k => condSet k Gcomb (minExtend (valStepValue v) k))

namespace valStep

theorem body_isScottContinuous (v : Pomega) :
    IsScottContinuous (fun k =>
      condSet k Gcomb (minExtend (valStepValue v) k)) :=
  theorem_1_3.tuple
    (fun y => condSet.isScottContinuous_left Gcomb y)
    (fun z => condSet.isScottContinuous_right z Gcomb)
    id_isScottContinuous
    (minExtend_isScottContinuous (valStepValue v))

theorem app (v k : Pomega) :
    funOf (valStep v) k =
      condSet k Gcomb (minExtend (valStepValue v) k) :=
  beta (body_isScottContinuous v) k

theorem app_zero (v : Pomega) :
    funOf (valStep v) (ofNat 0) = Gcomb := by
  rw [app]
  exact eq_2_7_zero Gcomb (minExtend (valStepValue v) (ofNat 0))

theorem app_succ (v : Pomega) (p : ℕ) :
    funOf (valStep v) (ofNat (p + 1)) =
      funOf (funOf v (ofNat (unpair p).1))
        (funOf v (ofNat (unpair p).2)) := by
  rw [app, eq_2_7_succ]
  simp [minExtend, valStepValue, ofNat]

end valStep

end DomainTheory.DataTypesAsLattices
