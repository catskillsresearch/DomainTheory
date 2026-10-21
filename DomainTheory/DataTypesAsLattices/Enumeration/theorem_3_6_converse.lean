/-ai
An element x belongs to the degree of the single generator of the singleton list of x. This is the singleton converse of Scott's Theorem 3.6: the packed generator recovers x in its own degree.

The finite-generation clause of Theorem 3.6 puts the packed list in that degree, and the numeral 0 lies in the degree because it is combinatory. The degree is a subalgebra, so the application of the packed list to the numeral 0 lies in the degree, and that application is x.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
    (Deg_isSubalgebra _).2 hp h0
  simpa [packList_cons_zero] using this

end DomainTheory.DataTypesAsLattices
