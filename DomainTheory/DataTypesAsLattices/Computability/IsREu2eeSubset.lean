module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.primrecPred_common_stage
public import DomainTheory.DataTypesAsLattices.Computability.eSubset_iff_stage

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- Finite inclusion `e n ⊆ x` is r.e. in `n` when `x` is, via one common `evaln` stage. -/
theorem IsRE.eSubset {x : Pomega} (hx : IsRE x) :
    REPred fun n => e n ⊆ x := by
  have hf : Partrec fun k : ℕ =>
      (Part.assert (k ∈ x) fun _ => Part.some (0 : ℕ)) :=
    hx.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hex : REPred fun n =>
      ∃ s, ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true :=
    REPred.exists (p := fun n s =>
        ∀ k < n, n.testBit k = false ∨ (evaln s c k).isSome = true)
      (primrecPred_common_stage c).computablePred.to_re
  exact hex.of_eq fun n => (eSubset_iff_stage hc n).symm

end DomainTheory.DataTypesAsLattices
