/-ai
If two compact fixed points of a closure operator are bounded above, the image of their supremum is again a compact fixed point.

Suppose that image lies below a directed supremum of fixed points. Inflation puts the supremum of the two points below the same directed supremum, and each of the two points lies below that supremum. Compactness supplies an index for each, and directedness supplies a common index above both. The supremum is the least upper bound of the two points, so it lies below the family value at that index. Monotonicity of the element map and the fixed-point equation for that value place the image below it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.le_toElementMap_of_isClosureOperator
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsCompactFix

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- **Finite joins of compacts are compact.** If `y₁, y₂ ∈ Fix(a)` are compact and bounded above
(in `E`), their join `a(⊔{y₁,y₂})` (`⊔` = Exercise 1.27's `sSup`) is again compact: if it sits below
a directed union, so do `y₁` and `y₂` individually (they are `⊑ a(⊔{y₁,y₂})` since `⊔ ⊑ a(⊔)` by
inflation), compactness places each below some member of the family, directedness finds a common
one, and the join being *least* upper bound of `{y₁,y₂}` (composed with `a`) transfers the bound. -/
theorem isCompactFix_sup (h : IsClosureOperator a) {y1 y2 : FixSet a}
    (hc1 : IsCompactFix h y1) (hc2 : IsCompactFix h y2)
    (hb : E.Bounded ({y1.1, y2.1} : Set E.Element)) :
    IsCompactFix h ⟨a.toElementMap (E.sSup {y1.1, y2.1} hb), toElementMap_idem h.1 _⟩ := by
  intro I _ d hdir hle
  have hs_le : E.sSup {y1.1, y2.1} hb ≤ iSupDirected (fun i => (d i).1) hdir :=
    (le_toElementMap_of_isClosureOperator h _).trans hle
  have h1le : y1.1 ≤ iSupDirected (fun i => (d i).1) hdir :=
    (E.le_sSup {y1.1, y2.1} hb (by simp)).trans hs_le
  have h2le : y2.1 ≤ iSupDirected (fun i => (d i).1) hdir :=
    (E.le_sSup {y1.1, y2.1} hb (by simp)).trans hs_le
  obtain ⟨i1, hi1⟩ := hc1 d hdir h1le
  obtain ⟨i2, hi2⟩ := hc2 d hdir h2le
  obtain ⟨k, hk1, hk2⟩ := hdir i1 i2
  have hle1 : y1.1 ≤ (d k).1 := hi1.trans hk1
  have hle2 : y2.1 ≤ (d k).1 := hi2.trans hk2
  have hsup_le : E.sSup {y1.1, y2.1} hb ≤ (d k).1 :=
    E.sSup_le {y1.1, y2.1} hb (by rintro x (rfl | rfl) <;> assumption)
  refine ⟨k, ?_⟩
  have h3 := a.toElementMap_mono hsup_le
  rwa [(d k).2] at h3

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
