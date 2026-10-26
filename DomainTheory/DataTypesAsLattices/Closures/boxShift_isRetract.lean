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
public import DomainTheory.DataTypesAsLattices.Closures.predSet_union
public import DomainTheory.DataTypesAsLattices.Closures.predSet_succSet
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxShift_isRetract {a : Pomega} (ha : Retract a) :
    Retract (boxShift a) := by
  constructor
  change boxShift a =
    graph (fun x => funOf (boxShift a) (funOf (boxShift a) x))
  apply graph_ext
  intro x
  rw [boxShift_app, boxShift_app]
  have hpred : predSet (ofNat 0 ∪ succSet (funOf a (predSet x))) =
      funOf a (predSet x) := by
    rw [predSet_union, predSet_ofNat_zero, predSet_succSet]
    simp [botElem]
  rw [hpred, retract_app ha]

end DomainTheory.DataTypesAsLattices
