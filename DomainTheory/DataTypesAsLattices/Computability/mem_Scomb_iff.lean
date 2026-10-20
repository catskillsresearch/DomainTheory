module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



theorem mem_Scomb_iff (p : ℕ) :
    p ∈ Scomb ↔
      ∃ n0 n1 n2 m, p = pair n0 (pair n1 (pair n2 m)) ∧
        m ∈ (e n0 ⬝ e n2) ⬝ (e n1 ⬝ e n2) := by
  constructor
  · intro ⟨n0, p1, hp, hp1⟩
    obtain ⟨n1, p2, hp1', hp2⟩ := hp1
    obtain ⟨n2, m, hp2', hm⟩ := hp2
    exact ⟨n0, n1, n2, m, by simp [hp, hp1', hp2'], hm⟩
  · intro ⟨n0, n1, n2, m, hp, hm⟩
    exact ⟨n0, pair n1 (pair n2 m), hp,
      ⟨n1, pair n2 m, rfl, ⟨n2, m, rfl, hm⟩⟩⟩

end DomainTheory.DataTypesAsLattices
