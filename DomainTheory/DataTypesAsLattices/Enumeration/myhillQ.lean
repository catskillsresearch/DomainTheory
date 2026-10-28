module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.fin
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def myhillQ (val : ℕ → Pomega) (p : ℕ → ℕ) : Pomega :=
  {k | ∃ j m, k = pair j m ∧ m ∈ val (p (fin j))}

namespace myhillQ

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (p : ℕ → ℕ) (x : Pomega) :
    funOf (myhillQ valNat p) x =
      ⋃ j, ⋃ (_ : e j ⊆ x), valNat (p (fin j)) := by
  ext m
  constructor
  · rintro ⟨j, hj, hpair⟩
    have hm : m ∈ valNat (p (fin j)) := by
      obtain ⟨j', m', hp, hm⟩ := hpair
      obtain ⟨rfl, rfl⟩ := pair_inj hp
      exact hm
    exact Set.mem_iUnion.mpr
      ⟨j, Set.mem_iUnion.mpr ⟨hj, hm⟩⟩
  · intro hm
    obtain ⟨j, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hj, hm⟩ := Set.mem_iUnion.mp hm
    exact ⟨j, hj, ⟨j, m, rfl, hm⟩⟩

end myhillQ

end DomainTheory.DataTypesAsLattices
