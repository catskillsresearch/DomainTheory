module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_zero
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.sucC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem Gpack_zero : funOf Gpack (ofNat 0) = sucC := by
  simp [Gpack, seq2_app_zero]

end DomainTheory.DataTypesAsLattices
