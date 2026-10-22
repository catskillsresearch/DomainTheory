module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_6

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.6, combinator form.**
`(λf : V∘→V. Y(f)) : (V∘→V) ∘→ V`. -/
theorem theorem_5_6_combinator :
    typed (comp Ycomb (arrowR Vcomb Vcomb))
      (arrowR (arrowR Vcomb Vcomb) Vcomb) := by
  rw [typed, arrowR_app]
  apply graph_ext
  intro f
  have hV : Closure Vcomb := theorem_5_5_universe.1
  have harr : Retract (arrowR Vcomb Vcomb) := theorem_5_3 hV hV
  have hf' : typed (funOf (arrowR Vcomb Vcomb) f) (arrowR Vcomb Vcomb) :=
    (retract_app harr f).symm
  have hy := theorem_5_6 hf'
  simp only [comp_app]
  rw [retract_app harr]
  exact hy

end DomainTheory.DataTypesAsLattices
