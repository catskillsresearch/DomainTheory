module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_20
public import Mathlib.Topology.Defs.Filter

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem isOpen_basicOpen (X : Set α) : IsOpen (V.basicOpen X) :=
  ⟨fun _ hx => ⟨X, hx, subset_rfl⟩⟩

theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.OpenFilter U :=
  ⟨fun h => h, fun h => h⟩

theorem isOpen_isUpperSet {U : Set V.Element} (hU : IsOpen U) :
    ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U := by
  intro x y hxU hxy
  obtain ⟨X, hX, hXU⟩ := hU.out x hxU
  exact hXU (hxy X hX)

theorem isOpen_iff_upper_basic (U : Set V.Element) :
    IsOpen U ↔
      (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
        (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U) := by
  constructor
  · intro hU
    exact ⟨V.isOpen_isUpperSet hU, hU.out⟩
  · rintro ⟨_, h2⟩
    exact ⟨h2⟩

theorem le_iff_isOpen_imp (x y : V.Element) :
    x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hxy U hU hxU
    exact V.isOpen_isUpperSet hU hxU hxy
  · intro h
    exact fun X hX => h (V.basicOpen X) (V.isOpen_basicOpen X) hX

example :
    (∀ {U : Set V.Element}, IsOpen U → ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
      (∀ X : Set α, IsOpen (V.basicOpen X)) ∧
      (∀ U : Set V.Element,
        IsOpen U ↔
          (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
            (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U)) ∧
      (∀ x y : V.Element, x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U) :=
  ⟨V.isOpen_isUpperSet, V.isOpen_basicOpen, V.isOpen_iff_upper_basic, V.le_iff_isOpen_imp⟩

theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
