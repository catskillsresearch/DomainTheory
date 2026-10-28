module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.RE
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gbar
public import DomainTheory.DataTypesAsLattices.Enumeration.enumComp
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_more
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem generatedSemigroup_mem_RE_FUN {u : Pomega} (hu : GeneratedSemigroup u) :
    u ∈ RE ∩ FUN := by
  induction hu with
  | R => exact ⟨Rcomb.combinatory, Rcomb.mem_FUN⟩
  | L => exact ⟨Lcomb.combinatory, Lcomb.mem_FUN⟩
  | Gbar => exact ⟨Gbar.combinatory, Gbar.mem_FUN⟩
  | comp _ _ ihu ihv =>
      exact ⟨enumComp.combinatory ihu.1 ihv.1, enumComp.mem_FUN _ _⟩

end DomainTheory.DataTypesAsLattices
