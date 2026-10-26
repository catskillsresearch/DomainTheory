module

public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Lambda.Kcomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Kcomb_app2 (x y : Pomega) : funOf (funOf Kcomb x) y = x := by
  rw [Kcomb_app]
  exact beta (const_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
