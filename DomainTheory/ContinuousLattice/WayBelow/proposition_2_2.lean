module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

/-- **Scott 1972, Proposition 2.2.** In a complete lattice:

(i) `⊥ ≪ x`;

(ii) `x ≪ z` and `y ≪ z` imply `x ⊔ y ≪ z`;

(iii) `x ≪ y` and `y ≤ z` imply `x ≪ z`;

(iv) `x ≤ y` and `y ≪ z` imply `x ≪ z`;

(v) `x ≪ y` implies `x ≤ y`;

(vi) `x ≪ x` iff `Set.Ici x` is Scott-open;

(vii) for a nonempty directed `S`, `x ≪ sSup S` iff `x ≪ y` for some `y ∈ S`.

Proved from `bot_wayBelow`, `WayBelow.sup`, `WayBelow.trans_le`, `WayBelow.le_trans`,
`WayBelow.le`, `WayBelow.self_iff_scottOpen_Ici`, and `WayBelow.sSup_iff`. -/
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
