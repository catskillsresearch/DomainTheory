module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isLambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eiff_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4








































/-- **Scott 1976, Theorem 2.6 (The definability theorem).**
For a `k`-ary continuous `f`, computability of the finite-argument relation,
recursive enumerability of the nested graph, combinatory definability, and
closed LAMBDA-definability agree. -/
theorem theorem_2_6_fin {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : IsScottContinuousFin f) :
    (IsComputableFin f ↔ IsRE (curryFin f)) ∧
      (IsRE (curryFin f) ↔ IsCombinatory (curryFin f)) ∧
      (IsLambdaDefinable (curryFin f) ↔ IsCombinatory (curryFin f)) := by
  refine ⟨?_, IsRE.iff_combinatory, ?_⟩
  · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
  · exact ⟨fun ⟨t, ht⟩ => by simpa [ht] using theorem_2_4_closed t,
      combinatory_isLambdaDefinable⟩

end DomainTheory.DataTypesAsLattices
