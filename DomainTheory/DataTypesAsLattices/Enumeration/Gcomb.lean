module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.sumMed
public import DomainTheory.DataTypesAsLattices.Functionality.Zcomb
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import DomainTheory.DataTypesAsLattices.Enumeration.Gpack
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta2
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_bot
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_succ
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_7_zero

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (3.3).** `G = cond(⟨suc, pred, cond, K, S⟩)(0)`. -/
def Gcomb : Pomega :=
  graph (fun z => condSet z Gpack zeroC)

namespace Gcomb

theorem eq_condC : Gcomb = funOf (funOf condC Gpack) zeroC :=
  (condC.beta2 Gpack zeroC).symm

theorem app (z : Pomega) :
    funOf Gcomb z = condSet z Gpack zeroC :=
  beta (condSet.isScottContinuous_left Gpack zeroC) z

theorem zero : funOf Gcomb (ofNat 0) = Gpack := by
  rw [app, eq_2_7_zero]

theorem bot : funOf Gcomb botElem = botElem := by
  rw [app, eq_2_7_bot]

theorem succ (k : ℕ) : funOf Gcomb (ofNat (k + 1)) = zeroC := by
  rw [app, eq_2_7_succ]

end Gcomb

end DomainTheory.DataTypesAsLattices
