module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

namespace ApproximableMap

section
variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

def iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) : ApproximableMap V₀ V₁ where
  rel X Z := ∃ i, (f i).rel X Z
  rel_dom := fun ⟨i, h⟩ => (f i).rel_dom h
  rel_cod := fun ⟨i, h⟩ => (f i).rel_cod h
  master_rel := by obtain ⟨i⟩ := (inferInstance : Nonempty I); exact ⟨i, (f i).master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (f k).inter_right (hik X Z hi) (hjk X Z' hj)⟩
  mono := by
    rintro X X' Z Z' ⟨i, hi⟩ hX'X hZZ' hX' hZ'
    exact ⟨i, (f i).mono hi hX'X hZZ' hX' hZ'⟩

theorem mem_toElementMap_iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) (x : V₀.Element) {Y : Set β} :
    ((iSupMap f hdir).toElementMap x).mem Y ↔ ∃ i, ((f i).toElementMap x).mem Y := by
  constructor
  · rintro ⟨X, hxX, i, hrel⟩
    exact ⟨i, X, hxX, hrel⟩
  · rintro ⟨i, X, hxX, hrel⟩
    exact ⟨X, hxX, i, hrel⟩
end

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
