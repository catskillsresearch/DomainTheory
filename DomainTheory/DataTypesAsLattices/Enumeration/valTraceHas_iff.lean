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









theorem valTraceHas_iff (tr : ValTrace) (c m : ℕ) :
    valTraceHas tr c m ↔ ∃ e ∈ tr, e.1 = c ∧ e.2.1 = m := by
  constructor
  · intro ⟨t, ht⟩
    exact ⟨(c, m, t), ht, rfl, rfl⟩
  · intro ⟨e, he, hc, hm⟩
    exact ⟨e.2.2, by cases e; cases hc; cases hm; exact he⟩

end DomainTheory.DataTypesAsLattices
