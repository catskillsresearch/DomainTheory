
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Kcomb_beta2 (x y : Pomega) : funOf (funOf Kcomb x) y = x := by
  rw [Kcomb_beta]
  exact beta (const_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
