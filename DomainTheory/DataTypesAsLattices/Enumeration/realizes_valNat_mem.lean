/-ai
If an element u realizes a function p, then a natural number m lies in val(p(n)) if and only if some code c lies in u applied to the numeral of n and m lies in val(c).

Rewrite by the realizing hypothesis. Membership of m in val(p(n)) is witnessed by the code p(n). Conversely, simplifying the numeral membership forces the witnessing code to equal p(n).
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
