/-ai
Scott 1976, section 7. A restricted equivalence is a symmetric and transitive relation on Pω, given by a binary relation together with symmetry and transitivity.
ai-/
module


public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §7, Definition.** A restricted equivalence is a
symmetric transitive relation, coded as a set of pairs. -/
structure RestrictedEquiv where
  rel : Pomega → Pomega → Prop
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

end DomainTheory.DataTypesAsLattices
