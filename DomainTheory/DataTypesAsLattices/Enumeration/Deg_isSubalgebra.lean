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
