module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem interp_avoids {i : ℕ} (t : Term) (ρ : ℕ → Pomega) (v : Pomega)
    (h : t.Avoids i) : interp t (envSet ρ i v) = interp t ρ := by
  induction t generalizing ρ i with
  | var j =>
    have hji : j ≠ i := h
    simp [interp, envSet, Function.update, hji]
  | zero => rfl
  | succ t ih => exact congrArg succSet (ih (ρ := ρ) (i := i) h)
  | pred t ih => exact congrArg predSet (ih (ρ := ρ) (i := i) h)
  | cond z x y ihz ihx ihy =>
    simp only [interp]
    rw [ihz (ρ := ρ) (i := i) h.1, ihx (ρ := ρ) (i := i) h.2.1,
      ihy (ρ := ρ) (i := i) h.2.2]
  | app u x ihu ihx =>
    simp only [interp]
    rw [ihu (ρ := ρ) (i := i) h.1, ihx (ρ := ρ) (i := i) h.2]
  | lam j body ih =>
    simp only [interp]
    apply congrArg graph
    funext w
    cases h with
    | inl hji =>
      subst hji
      simp [envSet]
    | inr hb =>
      by_cases hji : j = i
      · subst hji
        simp [envSet]
      · rw [envSet_comm (ρ := ρ) (i := i) (j := j) (Ne.symm hji) v w,
          ih (ρ := envSet ρ j w) (i := i) hb]

end DomainTheory.DataTypesAsLattices
