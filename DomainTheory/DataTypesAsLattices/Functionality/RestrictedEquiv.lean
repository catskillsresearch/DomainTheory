module

public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

end DomainTheory.DataTypesAsLattices
