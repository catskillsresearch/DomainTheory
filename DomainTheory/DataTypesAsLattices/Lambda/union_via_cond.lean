module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_15
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta3

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































/-- **Scott 1976, (2.15)** as a combinator: `cond(x)(y)(K(0)) = x ∪ y`. -/
theorem union_via_cond (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf Kcomb zeroC) = x ∪ y := by
  rw [condC_beta3, Kcomb_beta]
  exact eq_2_15 x y

end DomainTheory.DataTypesAsLattices
