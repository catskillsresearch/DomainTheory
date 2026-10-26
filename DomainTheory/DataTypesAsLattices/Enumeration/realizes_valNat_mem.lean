
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem realizes_valNat_mem {u : Pomega} {p : ℕ → ℕ} (hr : Realizes u p) (n m : ℕ) :
    m ∈ valNat (p n) ↔ ∃ c, c ∈ funOf u (ofNat n) ∧ m ∈ valNat c := by
  rw [hr]
  constructor
  · intro hm
    exact ⟨p n, rfl, hm⟩
  · intro ⟨c, hc, hm⟩
    simp [ofNat] at hc
    subst hc
    exact hm

end DomainTheory.DataTypesAsLattices
