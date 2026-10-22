module

public import Mathlib.Computability.RE
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


/-- **Scott 1976, Theorem 2.6 (The definability theorem), unary case.**
For a continuous `f`, computability, recursive enumerability of the graph,
combinatory definability, and closed LAMBDA-definability agree. -/
theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsRE (graph f) ↔ IsCombinatory (graph f)) ∧
      (LambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by
  refine ⟨?_, IsRE.iff_combinatory, ?_⟩
  · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
  · exact ⟨fun h => by
      obtain ⟨t, ht⟩ := h.out
      simpa [ht] using theorem_2_4_closed t,
      combinatory_isLambdaDefinable⟩

end DomainTheory.DataTypesAsLattices
