
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.interp_avoids

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem seqConsTerm_interp (a xs : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 7) (hxs : xs.Avoids 7) :
    interp (seqConsTerm a xs) ρ =
      seqCons (interp a ρ) (interp xs ρ) := by
  unfold seqConsTerm seqCons
  apply congrArg graph
  funext z
  simp only [interp]
  rw [interp_avoids a ρ z ha, interp_avoids xs ρ z hxs]
  simp [envSet, Function.update]

end DomainTheory.DataTypesAsLattices
