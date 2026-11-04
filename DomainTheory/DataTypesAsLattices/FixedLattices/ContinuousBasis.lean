module

public import DomainTheory.DataTypesAsLattices.FixedLattices.WayBelow

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

class ContinuousBasis {α : Type u} [CompleteLattice α]
    (basis : α → Set α) : Prop where
  out : ∀ x, @DirectedSet α completeLatticePreorder (basis x) ∧
    (∀ y ∈ basis x, WayBelow y x) ∧
    x = @sSup α completeLatticeSupSet (basis x)

end DomainTheory.DataTypesAsLattices
