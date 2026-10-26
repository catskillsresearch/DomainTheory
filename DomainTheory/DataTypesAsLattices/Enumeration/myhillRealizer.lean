module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.myhillQ
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def myhillRealizer (p : ℕ → ℕ) : Pomega → Pomega :=
  funOf (myhillQ valNat p)

namespace myhillRealizer

theorem isScottContinuous (p : ℕ → ℕ) :
    IsScottContinuous (myhillRealizer p) :=
  funOf.isScottContinuous _

end myhillRealizer

end DomainTheory.DataTypesAsLattices
