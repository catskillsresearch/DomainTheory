/-ai
The enumeration degree of any element a is a combinatory subalgebra.

The combinator G lies in the degree because the application of K to G is combinatory, and the beta law for K shows that this element applied to a returns G. If x and y lie in the degree, witnessed by combinatory elements r and s, then the application of S to r and then to s is combinatory, and the beta law for S shows that this element applied to a returns the application of x to y.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Deg_isSubalgebra (a : Pomega) : IsSubalgebra (Deg a) := by
  constructor
  · refine ⟨funOf Kcomb Gcomb, IsCombinatory.app .K Gcomb_combinatory, ?_⟩
    rw [Kcomb_beta2]
  · intro x y hx hy
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    refine ⟨funOf (funOf Scomb r) s, .app (.app .S hr) hs, ?_⟩
    rw [Scomb_beta3]

end DomainTheory.DataTypesAsLattices
