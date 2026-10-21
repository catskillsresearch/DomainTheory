/-ai
Binary application of natural-number codes is primitive recursive.

It agrees with the successor of the pairing function.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem primrec_applyNat : Primrec₂ applyNat :=
  (Primrec.succ.comp primrec_pair).of_eq fun _ => rfl

end DomainTheory.DataTypesAsLattices
