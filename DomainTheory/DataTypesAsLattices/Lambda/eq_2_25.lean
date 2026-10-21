/-ai
Scott 1976, (2.25). Applying the dollar combinator to u and then to x yields the union of the values uᵢ for i ∈ x.

The first application is the graph of sequence revaluation in its right argument, and the beta law for continuity in that argument gives the value.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.25).** `$ (u) = λx. ⋃ {u_i | i ∈ x}`. -/
theorem eq_2_25 (u x : Pomega) :
    funOf (funOf dollarC u) x = seqFun u x := by
  rw [dollarC_app]
  exact beta (seqFun_right_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
