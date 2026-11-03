module

public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Computability.IsComputable
public import DomainTheory.DataTypesAsLattices.Computability.LambdaDefinable
public import DomainTheory.DataTypesAsLattices.Computability.ComputableFin

import DomainTheory.DataTypesAsLattices.Computability.IsREu2eiff_combinatory
import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral
import DomainTheory.DataTypesAsLattices.Computability.combinatory_isLambdaDefinable
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_1
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem theorem_2_6 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (IsComputable f ↔ IsRE (graph f)) ∧
      (IsRE (graph f) ↔ IsCombinatory (graph f)) ∧
      (LambdaDefinable (graph f) ↔ IsCombinatory (graph f)) := by
  refine ⟨?_, IsRE.iff_combinatory, ?_⟩
  · exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩
  · exact ⟨fun h => by
      obtain ⟨t, ht⟩ := h.out
      simpa [ht] using theorem_2_4.closed t,
      combinatory_isLambdaDefinable⟩

namespace theorem_2_6

theorem combinatory_zero : LambdaDefinable zeroC :=
  ⟨⟨Term.zero, rfl⟩⟩

theorem fin {n : ℕ} {f : (Fin n → Pomega) → Pomega}
    (hf : ScottContinuousFin f) :
    (ComputableFin f ↔ IsRE (curryFin f)) ∧
      (IsRE (curryFin f) ↔ IsCombinatory (curryFin f)) ∧
      (LambdaDefinable (curryFin f) ↔ IsCombinatory (curryFin f)) := by
  refine ⟨?_, IsRE.iff_combinatory, ?_⟩
  · exact ⟨fun h => h.out.2, fun h => ⟨⟨hf, h⟩⟩⟩
  · exact ⟨fun h => by
      obtain ⟨t, ht⟩ := h.out
      simpa [ht] using theorem_2_4.closed t,
      combinatory_isLambdaDefinable⟩

theorem lambda_continuous (t : Term) :
    IsScottContinuous (fun v => interp t (envSet (fun _ => botElem) 0 v)) :=
  theorem_2_1 t (fun _ => botElem) 0

theorem ofNat_isRE (n : ℕ) : IsCombinatory (ofNat n) → IsRE (ofNat n) :=
  fun _ => IsRE.numeral n

end theorem_2_6

end DomainTheory.DataTypesAsLattices
