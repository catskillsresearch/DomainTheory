/-ai
The packed list of a finite list, and the combinator G, both belong to the degree of the single generator of that list. This is Scott's Theorem 3.6: the conditional of the packed list applied to G, and then to 0, is the packed tuple, and G lies in its degree.

The packed list is the application of S(I)(K 0), where I is S K K, to the single generator. That combinator is combinatory, being built from S, K, and zero. The three-place S equation, the identity equation, the two-place K equation, and the zero-application of the single generator show that the application equals the packed list. The combinator G belongs to the degree because every degree is a subalgebra.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Icomb_SK_app
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.singleGenerator_app_zero

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


/-- **Scott 1976, Theorem 3.6.** `cond(⟨xs⟩)(G)` applied to `0` is the
packed tuple, and `G` is in its degree. -/
theorem theorem_3_6_finite (xs : List Pomega) :
    packList xs ∈ Deg (singleGenerator xs) ∧
      Gcomb ∈ Deg (singleGenerator xs) := by
  constructor
  · refine ⟨funOf (funOf Scomb Icomb_SK) (funOf Kcomb zeroC),
      .app (.app .S (.app (.app .S .K) .K)) (.app .K .zero), ?_⟩
    rw [Scomb_beta3, Icomb_SK_app, Kcomb_beta2, singleGenerator_app_zero]
  · exact (Deg_isSubalgebra (singleGenerator xs)).1

end DomainTheory.DataTypesAsLattices
