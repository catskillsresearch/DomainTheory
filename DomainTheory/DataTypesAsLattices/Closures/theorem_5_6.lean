/-ai
Scott's limit theorem for algebraic lattices says that if a set is typed by the function space of the universe combinator with itself, then the application of the fixed-point combinator to that set is typed by the universe combinator.

The fixed-point combinator unfolds, so the application equals the set applied to itself. Typing in the function space rewrites each application of the set as an application of the universe combinator to the set applied after the universe combinator, and substituting the fixed point gives the fixed point as that rewritten application. Applying the universe combinator to the unfolding, rewriting the inner application by the same typing equation, and collapsing the double application because the universe combinator is a retract, shows that the universe combinator applied to the fixed point equals the fixed point. Reading that chain in reverse is the typing equation.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 5.6 (The limit theorem for algebraic lattices).**
`(λf : V∘→V. Y(f)) : (V∘→V) ∘→ V`. -/
theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by
  set y := funOf Ycomb f
  have hy : y = funOf f y := Ycomb_unfold f
  have hf' : ∀ x, funOf f x = funOf Vcomb (funOf f (funOf Vcomb x)) := by
    intro x
    simpa [comp_app] using congrArg (fun w => funOf w x) (typed_of_arrowR hf)
  have hyV : y = funOf Vcomb (funOf f (funOf Vcomb y)) :=
    hy.trans (hf' y)
  have h1 : funOf Vcomb y = funOf Vcomb (funOf f y) :=
    congrArg (funOf Vcomb) hy
  have h2 : funOf Vcomb (funOf f y) =
      funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) :=
    congrArg (funOf Vcomb) (hf' y)
  have h3 : funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) =
      funOf Vcomb (funOf f (funOf Vcomb y)) :=
    retract_app Vcomb_isRetract _
  exact (h1.trans (h2.trans (h3.trans hyV.symm))).symm

end DomainTheory.DataTypesAsLattices
