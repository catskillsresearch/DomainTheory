/-ai
In combinator form, Scott's limit theorem says that the composite of the fixed-point combinator with the function space of the universe combinator with itself is typed by the function space from that function space into the universe combinator.

After the typing equation and the application law, the two sides are graphs, so it is enough that they agree on each argument. The universe combinator is a closure, so its function space with itself is a retract. The retract equation types the retracted argument by that function space, the limit theorem types the fixed-point combinator applied to that argument by the universe combinator, and rewriting by the retract equation is the required value of the composite.
ai-/
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
  have hV : IsClosure Vcomb := theorem_5_5_universe.1
  have harr : Retract (arrowR Vcomb Vcomb) := theorem_5_3 hV hV
  have hf' : typed (funOf (arrowR Vcomb Vcomb) f) (arrowR Vcomb Vcomb) :=
    (retract_app harr f).symm
  have hy := theorem_5_6 hf'
  simp only [comp_app]
  rw [retract_app harr]
  exact hy

end DomainTheory.DataTypesAsLattices
