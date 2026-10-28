module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

namespace ApproximableMap

section
variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

def ofMono (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX') :
    ApproximableMap V₀ V₁ where
  rel X Y := ∃ hX : V₀.mem X, (m X hX).mem Y
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨hX, hY⟩ => (m _ hX).sub hY
  master_rel := ⟨V₀.master_mem, (m _ V₀.master_mem).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (m X hX).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    have hle : m X hX ≤ m X' hX' := hmono X X' hX hX' hX'X
    exact ⟨hX', (m X' hX').up_mem (hle Y hY) hY' hYY'⟩

theorem eq_of_toElementMap_principal {f g : ApproximableMap V₀ V₁}
    (h : ∀ (X : Set α) (hX : V₀.mem X),
      f.toElementMap (V₀.principal hX) = g.toElementMap (V₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h X hX]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

theorem toElementMap_ofMono_principal
    (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX')
    (X : Set α) (hX : V₀.mem X) :
    (ofMono m hmono).toElementMap (V₀.principal hX) = m X hX := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨Z, ⟨hZmem, hXZ⟩, hZ', hmY⟩
    have hle : m Z hZ' ≤ m X hX := hmono Z X hZ' hX hXZ
    exact hle Y hmY
  · intro hmY
    exact ⟨X, ⟨hX, subset_rfl⟩, hX, hmY⟩
end

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
