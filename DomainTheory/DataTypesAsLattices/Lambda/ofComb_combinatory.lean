/-ai
If every value of an environment is combinatory, then the interpretation of any combinatory term in that environment is combinatory.

The proof is by induction on the combinator. A variable uses the hypothesis on the environment. Zero, successor, predecessor, conditional, K, and S are the corresponding combinatory constructors. An application is the application constructor applied to the two inductive results.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem ofComb_combinatory (c : Comb) (ρ : ℕ → Pomega)
    (hρ : ∀ i, IsCombinatory (ρ i)) :
    IsCombinatory (ofComb c ρ) := by
  induction c with
  | var i => exact hρ i
  | zero => exact .zero
  | suc => exact .suc
  | pred => exact .pred
  | cond => exact .cond
  | K => exact .K
  | S => exact .S
  | app _ _ iu iv => exact .app iu iv

end DomainTheory.DataTypesAsLattices
