module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.envSet
public import DomainTheory.DataTypesAsLattices.Lambda.interp
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.Avoids
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
    simp [_root_.DomainTheory.DataTypesAsLattices.interp, envSet, Function.update, hji]
  | zero => rfl
  | succ t ih => exact congrArg succSet (ih (ρ := ρ) (i := i) h)
  | pred t ih => exact congrArg predSet (ih (ρ := ρ) (i := i) h)
  | cond z x y ihz ihx ihy =>
    simp only [_root_.DomainTheory.DataTypesAsLattices.interp]
    rw [ihz (ρ := ρ) (i := i) h.1, ihx (ρ := ρ) (i := i) h.2.1,
      ihy (ρ := ρ) (i := i) h.2.2]
  | app u x ihu ihx =>
    simp only [_root_.DomainTheory.DataTypesAsLattices.interp]
    rw [ihu (ρ := ρ) (i := i) h.1, ihx (ρ := ρ) (i := i) h.2]
  | lam j body ih =>
    simp only [_root_.DomainTheory.DataTypesAsLattices.interp]
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
      · rw [envSet.comm (ρ := ρ) (i := i) (j := j) (Ne.symm hji) v w,
          ih (ρ := envSet ρ j w) (i := i) hb]

end DomainTheory.DataTypesAsLattices
