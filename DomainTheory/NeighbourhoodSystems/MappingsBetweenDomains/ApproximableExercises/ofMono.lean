module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.ApproximableMap₂

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.8 (extension).** *Any* monotone function on finite elements comes from an
approximable map. Here a "monotone function on finite elements" is a map `m` sending each
neighbourhood `X` (a finite element `↑X`) to an element `m X hX : |𝒟₁|`, monotone in the sense
`X' ⊆ X → m X hX ≤ m X' hX'` (i.e. `↑X ⊑ ↑X' ⟹ m(↑X) ⊑ m(↑X')`). The induced relation is
`X f Y ↔ Y ∈ m(↑X)`. -/
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

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
