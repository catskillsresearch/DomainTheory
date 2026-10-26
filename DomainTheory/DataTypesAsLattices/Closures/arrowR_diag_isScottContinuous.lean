
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Isolated
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxTensor
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

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem arrowR_diag_isScottContinuous :
    IsScottContinuous (fun a => arrowR a a) := by
  have hbody : ∀ u, IsScottContinuous (fun a =>
      graph (fun x => funOf a (funOf u (funOf a x)))) :=
    fun u =>
      graph_const_isScottContinuous
        (fun a x => funOf a (funOf u (funOf a x)))
        (fun x =>
          theorem_1_3_tuple
            (f := fun a b => funOf a (funOf u (funOf b x)))
            (fun b => funOf_isScottContinuous_left (funOf u (funOf b x)))
            (fun a =>
              theorem_1_3 (funOf_isScottContinuous a)
                (theorem_1_3 (funOf_isScottContinuous u)
                  (funOf_isScottContinuous_left x)))
            id_isScottContinuous id_isScottContinuous)
  have heq : (fun a => arrowR a a) = (fun a =>
      graph (fun u => graph (fun x => funOf a (funOf u (funOf a x))))) := by
    funext a
    apply congrArg graph
    funext u
    change graph (fun x => funOf a (funOf (comp u a) x)) =
      graph (fun x => funOf a (funOf u (funOf a x)))
    apply congrArg graph
    funext x
    rw [comp_app]
  rw [heq]
  exact graph_const_isScottContinuous
    (fun a u => graph (fun x => funOf a (funOf u (funOf a x))))
    hbody

end DomainTheory.DataTypesAsLattices
