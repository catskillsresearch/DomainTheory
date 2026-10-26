module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem bar_generated {u : Pomega} (hu : GeneratedFromG u) :
    GeneratedSemigroup (funOf barComb u) := by
  induction hu with
  | G => exact GeneratedSemigroup.Gbar
  | app _ _ ihu ihv =>
      rw [← eq_3_17]
      exact .comp ihu (.comp ihv .R)

end DomainTheory.DataTypesAsLattices
