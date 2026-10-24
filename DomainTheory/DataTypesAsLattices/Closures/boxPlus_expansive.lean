module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Isolated
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
public import DomainTheory.DataTypesAsLattices.Closures.boxShift
public import DomainTheory.DataTypesAsLattices.Closures.boxTag
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact
public import DomainTheory.DataTypesAsLattices.Closures.compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.Vstep
public import DomainTheory.DataTypesAsLattices.Closures.VapplyY
public import DomainTheory.DataTypesAsLattices.Closures.closureRangeCountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode
public import DomainTheory.DataTypesAsLattices.Closures.representationOrderIso
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep
public import DomainTheory.DataTypesAsLattices.Closures.dEq
public import DomainTheory.DataTypesAsLattices.Closures.boool
public import DomainTheory.DataTypesAsLattices.Closures.closure_expansive
public import DomainTheory.DataTypesAsLattices.Closures.closureCompact_isCompact
public import DomainTheory.DataTypesAsLattices.Closures.compact_fixed_iff
public import DomainTheory.DataTypesAsLattices.Closures.retractBasis_eq_compactFixedBelow
public import DomainTheory.DataTypesAsLattices.Closures.fixed_eq_sSup_compacts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_mono
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode_app
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode_encode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode_fixed
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_mono
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_bot_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.4 (sum half), expansiveness.** Each of the four
occupancy cases of (5.13) is expansive: on a one-sided `u` the shift `a'`
is expansive by `boxShift_expansive` and (5.8) rebuilds `u`, while mixed
`u` goes to `⊤` and empty `u` is `⊥`. -/
theorem boxPlus_expansive {a b : Pomega} (ha : Closure a) (hb : Closure b)
    (u : Pomega) : u ⊆ funOf (boxPlus a b) u := by
  have h8 : squarePair (squareFst u) (squareSnd u) = u := eq_5_8 u
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [hx, hy, squarePair_bot_bot] at h8
    rw [boxPlus_app_empty hx hy, ← h8]
  · rw [boxPlus_app_right hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
      rw [hx]
      exact squarePair_mono subset_rfl (boxShift_expansive hb (squareSnd u))
    rwa [h8] at hsub
  · rw [boxPlus_app_left hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair (funOf (boxShift a) (squareFst u)) botElem := by
      rw [hy]
      exact squarePair_mono (boxShift_expansive ha (squareFst u)) subset_rfl
    rwa [h8] at hsub
  · rw [boxPlus_app_mixed hx hy]
    exact fun k _ => Set.mem_univ k

end DomainTheory.DataTypesAsLattices
