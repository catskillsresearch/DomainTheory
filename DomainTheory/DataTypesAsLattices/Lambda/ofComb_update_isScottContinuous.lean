/-ai
The interpretation of a combinatory term is Scott continuous in any one coordinate of the environment.

The proof is by induction on the combinator. A variable is the identity or a constant, according as its index is the varied coordinate. Each constant combinator is continuous as a constant. An application is the tuple form of Theorem 1.3, using continuity of application in each argument and the two inductive hypotheses.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem ofComb_update_isScottContinuous (c : Comb) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => ofComb c (envSet ρ i v)) := by
  induction c generalizing ρ i with
  | var j =>
    intro x
    by_cases hj : j = i
    · subst hj; simpa [ofComb, envSet, Function.update] using id_isScottContinuous x
    · simpa [ofComb, envSet, Function.update, hj] using const_isScottContinuous (ρ j) x
  | zero => intro x; simpa [ofComb] using const_isScottContinuous zeroC x
  | suc => intro x; simpa [ofComb] using const_isScottContinuous sucC x
  | pred => intro x; simpa [ofComb] using const_isScottContinuous predC x
  | cond => intro x; simpa [ofComb] using const_isScottContinuous condC x
  | K => intro x; simpa [ofComb] using const_isScottContinuous Kcomb x
  | S => intro x; simpa [ofComb] using const_isScottContinuous Scomb x
  | app u v iu iv =>
    exact theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun t => funOf_isScottContinuous t)
      (iu ρ i) (iv ρ i)

end DomainTheory.DataTypesAsLattices
