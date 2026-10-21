/-ai
Scott 1976, (2.15), as a combinator. The conditional applied to x, then to y, then to K applied to zero, equals the union of x and y.

Rewrite by the three-argument β-law for the conditional and the β-law for K, then apply equation (2.15).
ai-/
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
