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
