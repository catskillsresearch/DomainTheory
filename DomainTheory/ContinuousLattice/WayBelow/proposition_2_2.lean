module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

theorem proposition_2_2 :
    (∀ x : D, (⊥ : D) ≪ x) ∧
    (∀ x y z : D, x ≪ z → y ≪ z → x ⊔ y ≪ z) ∧
    (∀ x y z : D, x ≪ y → y ≤ z → x ≪ z) ∧
    (∀ x y z : D, x ≤ y → y ≪ z → x ≪ z) ∧
    (∀ x y : D, x ≪ y → x ≤ y) ∧
    (∀ x : D, x ≪ x ↔ ScottOpen (Set.Ici x)) ∧
    (∀ (x : D) (S : Set D), S.Nonempty → DirectedOn (· ≤ ·) S →
      (x ≪ sSup S ↔ ∃ y ∈ S, x ≪ y)) :=
  ⟨bot_wayBelow,
    fun _ _ _ hx hy => WayBelow.sup hx hy,
    fun _ _ _ h hyz => WayBelow.trans_le h hyz,
    fun _ _ _ hxy h => WayBelow.le_trans hxy h,
    fun _ _ h => WayBelow.le h,
    fun _ => WayBelow.self_iff_scottOpen_Ici,
    fun _ _ hS hdir => WayBelow.sSup_iff hS hdir⟩

end DomainTheory.ContinuousLattice
