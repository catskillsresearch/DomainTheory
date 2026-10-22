
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.packList_cons_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6_finite
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_Deg

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


/-- **Scott 1976, Theorem 3.6 converse (singleton).** The packed
generator recovers `x` in its own degree. -/
theorem theorem_3_6_converse (x : Pomega) :
    x ∈ Deg (singleGenerator [x]) := by
  have hp := (theorem_3_6_finite [x]).1
  have h0 := combinatory_mem_Deg (singleGenerator [x]) (ofNat_combinatory 0)
  have : funOf (packList [x]) (ofNat 0) ∈ Deg (singleGenerator [x]) :=
    (Deg_isSubalgebra _).out.2 hp h0
  simpa [packList_cons_zero] using this

end DomainTheory.DataTypesAsLattices
