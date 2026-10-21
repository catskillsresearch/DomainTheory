/-ai
Interpretation of the Y term in the constantly bottom environment equals the combinator Y.

This is simplification by the definitions of the term, interpretation, Y, the omega combinator, environment update, and function update.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















































theorem Yterm_interp : interp Yterm (fun _ => botElem) = Ycomb := by
  simp [Yterm, interp, Ycomb, omegaComb, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
