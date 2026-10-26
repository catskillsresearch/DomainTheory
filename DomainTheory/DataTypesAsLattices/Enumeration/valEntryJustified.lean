module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.unpairComp
public import DomainTheory.DataTypesAsLattices.Enumeration.ValTrace
public import DomainTheory.DataTypesAsLattices.Enumeration.valTraceHas

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def valEntryJustified (tr : ValTrace) (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 = 0 ∨
    (valTraceHas tr (unpairComp e.1.pred).1 (pair e.2.2 e.2.1) ∧
      ∀ i < e.2.2 + 1,
        e.2.2.testBit i = false ∨ valTraceHas tr (unpairComp e.1.pred).2 i)

namespace valEntryJustified

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem mono {tr₁ tr₂ : ValTrace} {e : ℕ × ℕ × ℕ}
    (hsub : ∀ c m, valTraceHas tr₁ c m → valTraceHas tr₂ c m)
    (h : valEntryJustified tr₁ e) : valEntryJustified tr₂ e := by
  rcases h with h | ⟨hop, hbits⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsub _ _ hop, fun i hi => (hbits i hi).imp_right (hsub _ _)⟩

end valEntryJustified

end DomainTheory.DataTypesAsLattices
