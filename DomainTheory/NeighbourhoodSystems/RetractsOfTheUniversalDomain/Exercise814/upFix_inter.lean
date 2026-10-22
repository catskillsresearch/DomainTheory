module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.le_toElementMap_of_isClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.joinCompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.le_sSup
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.sSup_le
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- **The key algebraic identity**: the intersection of two principal up-sets, when jointly
bounded by some `y`, is again a principal up-set — of the join. -/
theorem upFix_inter (k1 k2 : CompactFix h) {y : FixSet a}
    (hk1y : k1.1.1 ≤ y.1) (hk2y : k2.1.1 ≤ y.1) :
    upFix h k1 ∩ upFix h k2 = upFix h (joinCompactFix h hk1y hk2y) := by
  have hb : E.Bounded ({k1.1.1, k2.1.1} : Set E.Element) :=
    ⟨y.1, by rintro x (rfl | rfl) <;> assumption⟩
  apply Set.ext
  intro q
  simp only [mem_upFix, Set.mem_inter_iff, joinCompactFix]
  constructor
  · rintro ⟨h1q, h2q⟩
    have hb' : E.Bounded ({k1.1.1, k2.1.1} : Set E.Element) :=
      ⟨q.1.1, by rintro x (rfl | rfl) <;> assumption⟩
    have hsup_le : E.sSup {k1.1.1, k2.1.1} hb' ≤ q.1.1 :=
      E.sSup_le {k1.1.1, k2.1.1} hb' (by rintro x (rfl | rfl) <;> assumption)
    have h3 := a.toElementMap_mono hsup_le
    rwa [q.1.2] at h3
  · intro hjq
    refine ⟨?_, ?_⟩
    · exact ((E.le_sSup {k1.1.1, k2.1.1} hb (by simp)).trans
        (le_toElementMap_of_isClosureOperator h _)).trans hjq
    · exact ((E.le_sSup {k1.1.1, k2.1.1} hb (by simp)).trans
        (le_toElementMap_of_isClosureOperator h _)).trans hjq

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
