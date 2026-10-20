module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.joinCompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

theorem joinCompactFix_le {k1 k2 : CompactFix h} {y : FixSet a}
    (hk1y : k1.1.1 ≤ y.1) (hk2y : k2.1.1 ≤ y.1) : (joinCompactFix h hk1y hk2y).1.1 ≤ y.1 := by
  have hb : E.Bounded ({k1.1.1, k2.1.1} : Set E.Element) :=
    ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩
  have hsup_le : E.sSup {k1.1.1, k2.1.1} hb ≤ y.1 :=
    E.sSup_le {k1.1.1, k2.1.1} hb (by rintro x (rfl | rfl) <;> assumption)
  have h1 := a.toElementMap_mono hsup_le
  rwa [y.2] at h1

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
