/-ai
A third application of S, at x, equals the application of f at x applied to g at x.

Rewrite by the second beta law for S, then beta-reduce, using Scott continuity of the inner map at f and g.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_inner_cont
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_beta3 (f g x : Pomega) :
    funOf (funOf (funOf Scomb f) g) x = funOf (funOf f x) (funOf g x) := by
  rw [Scomb_beta2]
  exact beta (Scomb_inner_cont f g) x

end DomainTheory.DataTypesAsLattices
