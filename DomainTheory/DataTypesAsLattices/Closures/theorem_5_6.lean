module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.iterateFrom
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_isClosure
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_more
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by
  set y := funOf Ycomb f
  have hy : y = funOf f y := Ycomb.unfold f
  have hf' : ∀ x, funOf f x = funOf Vcomb (funOf f (funOf Vcomb x)) := by
    intro x
    simpa [comp.app] using congrArg (fun w => funOf w x) (arrowR.typed_of hf)
  have hyV : y = funOf Vcomb (funOf f (funOf Vcomb y)) :=
    hy.trans (hf' y)
  have h1 : funOf Vcomb y = funOf Vcomb (funOf f y) :=
    congrArg (funOf Vcomb) hy
  have h2 : funOf Vcomb (funOf f y) =
      funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) :=
    congrArg (funOf Vcomb) (hf' y)
  have h3 : funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) =
      funOf Vcomb (funOf f (funOf Vcomb y)) :=
    retract_app Vcomb.isRetract _
  exact (h1.trans (h2.trans (h3.trans hyV.symm))).symm

namespace theorem_5_6

theorem combinator :
    typed (comp Ycomb (arrowR Vcomb Vcomb))
      (arrowR (arrowR Vcomb Vcomb) Vcomb) := by
  rw [typed, arrowR.app]
  apply graph_ext
  intro f
  have hV : Closure Vcomb := theorem_5_5.universe.1
  have harr : Retract (arrowR Vcomb Vcomb) := theorem_5_3 hV hV
  have hf' : typed (funOf (arrowR Vcomb Vcomb) f) (arrowR Vcomb Vcomb) :=
    (retract_app harr f).symm
  have hy := theorem_5_6 hf'
  simp only [comp.app]
  rw [retract_app harr]
  exact hy

theorem iterates {F : Pomega → Pomega}
    (_hF : IsScottContinuous F)
    (hcl : ∀ a, Closure a → Closure (F a)) :
    (∀ n, Closure (iterateFrom F Icomb n)) ∧
      Icomb ⊆ lfpAbove F Icomb := by
  have hiter : ∀ n, Closure (iterateFrom F Icomb n) := by
    intro n
    induction n with
    | zero => exact Icomb_isClosure
    | succ n ih => exact hcl _ ih
  exact ⟨hiter, Set.subset_iUnion (iterateFrom F Icomb) 0⟩

end theorem_5_6

end DomainTheory.DataTypesAsLattices
