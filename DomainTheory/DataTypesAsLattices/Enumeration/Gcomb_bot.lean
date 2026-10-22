module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem Gcomb_bot : funOf Gcomb botElem = botElem := by
  rw [Gcomb_app, eq_2_7_bot]

end DomainTheory.DataTypesAsLattices
