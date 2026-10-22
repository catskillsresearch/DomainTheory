module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.isCompactFix_sup
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- The join of two compact fixed points bounded above by a common `y ∈ Fix(a)`. -/
def joinCompactFix {k1 k2 : CompactFix h} {y : FixSet a}
    (hk1y : k1.1.1 ≤ y.1) (hk2y : k2.1.1 ≤ y.1) : CompactFix h :=
  ⟨⟨a.toElementMap (E.sSup {k1.1.1, k2.1.1} ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩),
      toElementMap_idem h.out.1 _⟩,
    isCompactFix_sup h k1.2 k2.2 ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
