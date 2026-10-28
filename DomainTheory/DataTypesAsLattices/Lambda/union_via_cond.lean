module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_15
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Lambda.condC
public import DomainTheory.DataTypesAsLattices.Lambda.zeroC
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_more
public import DomainTheory.DataTypesAsLattices.Lambda.condC_more
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem union_via_cond (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf Kcomb zeroC) = x ∪ y := by
  rw [condC.beta3, Kcomb.beta]
  exact eq_2_15 x y

end DomainTheory.DataTypesAsLattices
