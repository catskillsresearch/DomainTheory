module

public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

namespace RestrictedEquiv

def mem (A : RestrictedEquiv) (x : Pomega) : Prop :=
  A.rel x x

end RestrictedEquiv

end DomainTheory.DataTypesAsLattices
