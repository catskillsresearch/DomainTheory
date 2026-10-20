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









theorem valEntryJustified_mono {tr₁ tr₂ : ValTrace} {e : ℕ × ℕ × ℕ}
    (hsub : ∀ c m, valTraceHas tr₁ c m → valTraceHas tr₂ c m)
    (h : valEntryJustified tr₁ e) : valEntryJustified tr₂ e := by
  rcases h with h | ⟨hop, hbits⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsub _ _ hop, fun i hi => (hbits i hi).imp_right (hsub _ _)⟩

end DomainTheory.DataTypesAsLattices
