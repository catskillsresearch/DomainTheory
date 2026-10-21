/-ai
Two enumerated sum neighbourhoods are equal if and only if both tags lie off zero and one, or both tags are zero and the first components agree, or both tags are one and the second components agree.

Split both tags by the trichotomy. Two left copies reduce to equality of the components by injectivity of the left copy, and the other Boolean branches contradict the tags. Two right copies do the same for the right copy. Two masters are equal outright. A left copy differs from a right copy because the second presentation's neighbourhood is nonempty, and each copy differs from the master. In every mixed case the Boolean branches contradict the tags.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.tag_trichotomy
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₁_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_ne_sumMaster
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₁_ne_sumMaster
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.inj₀_ne_inj₁_of_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

include h₁ in
/-- **Equality of two sum-neighbourhoods, in the indices.** Both master, or same tag with equal
component. -/
theorem sumEnum_eq_iff (x y : ℕ) :
    sumEnum P₀ P₁ x = sumEnum P₀ P₁ y ↔
      ((x.unpair.1 ≠ 0 ∧ x.unpair.1 ≠ 1) ∧ (y.unpair.1 ≠ 0 ∧ y.unpair.1 ≠ 1))
        ∨ (((x.unpair.1 = 0 ∧ y.unpair.1 = 0) ∧ P₀.X x.unpair.2 = P₀.X y.unpair.2)
          ∨ ((x.unpair.1 = 1 ∧ y.unpair.1 = 1) ∧ P₁.X x.unpair.2 = P₁.X y.unpair.2)) := by
  rcases tag_trichotomy x.unpair.1 with hx | hx | ⟨hx0, hx1⟩ <;>
    rcases tag_trichotomy y.unpair.1 with hy | hy | ⟨hy0, hy1⟩
  · -- x0 y0
    rw [sumEnum_zero hx, sumEnum_zero hy, inj₀_eq_iff]
    constructor
    · intro he; exact Or.inr (Or.inl ⟨⟨hx, hy⟩, he⟩)
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨_, he⟩ | ⟨⟨e1, e2⟩, _⟩)
      · exfalso; omega
      · exact he
      · exfalso; omega
  · -- x0 y1
    rw [sumEnum_zero hx, sumEnum_one hy]
    constructor
    · intro h; exact absurd h (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- x0 yM
    rw [sumEnum_zero hx, sumEnum_master hy0 hy1]
    constructor
    · intro h; exact absurd h inj₀_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- x1 y0
    rw [sumEnum_one hx, sumEnum_zero hy]
    constructor
    · intro h; exact absurd h.symm (inj₀_ne_inj₁_of_nonempty (h₁ _ (P₁.mem_X _)))
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- x1 y1
    rw [sumEnum_one hx, sumEnum_one hy, inj₁_eq_iff]
    constructor
    · intro he; exact Or.inr (Or.inr ⟨⟨hx, hy⟩, he⟩)
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨_, he⟩)
      · exfalso; omega
      · exfalso; omega
      · exact he
  · -- x1 yM
    rw [sumEnum_one hx, sumEnum_master hy0 hy1]
    constructor
    · intro h; exact absurd h inj₁_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- xM y0
    rw [sumEnum_master hx0 hx1, sumEnum_zero hy]
    constructor
    · intro h; exact absurd h.symm inj₀_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- xM y1
    rw [sumEnum_master hx0 hx1, sumEnum_one hy]
    constructor
    · intro h; exact absurd h.symm inj₁_ne_sumMaster
    · rintro (⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ | ⟨⟨e1, e2⟩, _⟩ | ⟨⟨e1, e2⟩, _⟩) <;> exfalso <;> omega
  · -- xM yM
    rw [sumEnum_master hx0 hx1, sumEnum_master hy0 hy1]
    exact ⟨fun _ => Or.inl ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, fun _ => rfl⟩

end Sum

end DomainTheory.NeighbourhoodSystems
