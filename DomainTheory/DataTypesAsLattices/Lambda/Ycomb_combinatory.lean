/-ai
The combinator Y is combinatory.

The closed case of Theorem 2.4 applies to the Y term, and the interpretation of that term rewrites the result.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_closed
public import DomainTheory.DataTypesAsLattices.Lambda.Yterm_interp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















































theorem Ycomb_combinatory : IsCombinatory Ycomb := by
  simpa [Yterm_interp] using theorem_2_4_closed Yterm

end DomainTheory.DataTypesAsLattices
