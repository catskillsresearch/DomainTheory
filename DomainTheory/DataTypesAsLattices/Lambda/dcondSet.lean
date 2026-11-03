module

public import DomainTheory.DataTypesAsLattices.Lambda.condSet
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Doubly strict conditional (Scott (4.4)):
    `z ⊐ x, y = z ⊃ (z ⊃ x, ⊤), (z ⊃ ⊤, y)`. -/
def dcondSet (z x y : Pomega) : Pomega :=
  condSet z (condSet z x topElem) (condSet z topElem y)

namespace dcondSet

theorem isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => dcondSet z x y) :=
  theorem_1_3.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    id_isScottContinuous
    (condSet.isScottContinuous_left x topElem)
    (condSet.isScottContinuous_left topElem y)

theorem bot (x y : Pomega) : dcondSet botElem x y = botElem := by
  ext n
  simp [dcondSet, condSet, botElem]

theorem cases (z : Pomega) :
    (0 ∈ z ∧ ¬ ∃ k, k + 1 ∈ z) ∨
      (0 ∉ z ∧ ∃ k, k + 1 ∈ z) ∨
        (0 ∈ z ∧ ∃ k, k + 1 ∈ z) ∨
          (0 ∉ z ∧ ¬ ∃ k, k + 1 ∈ z) := by
  by_cases h0 : 0 ∈ z
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inr (Or.inl ⟨h0, hp⟩))
    · exact Or.inl ⟨h0, hp⟩
  · by_cases hp : ∃ k, k + 1 ∈ z
    · exact Or.inr (Or.inl ⟨h0, hp⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h0, hp⟩))

theorem isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z w (condSet z topElem y))
    (g := fun x => condSet z x topElem)
    (condSet.isScottContinuous_mid z (condSet z topElem y))
    (condSet.isScottContinuous_mid z topElem)

theorem isScottContinuous_right (z x : Pomega) :
    IsScottContinuous (fun y => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z (condSet z x topElem) w)
    (g := fun y => condSet z topElem y)
    (condSet.isScottContinuous_right z (condSet z x topElem))
    (condSet.isScottContinuous_right z topElem)

theorem of_empty {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = botElem := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨_, ht⟩
    · exact (h0 hz).elim
    · exact (hp ht).elim
  · intro hn
    simp [botElem] at hn

theorem of_mixed {z x y : Pomega}
    (h0 : 0 ∈ z) (hp : ∃ k, k + 1 ∈ z) :
    dcondSet z x y = topElem := by
  have hL : condSet z x topElem = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inr ⟨Set.mem_univ n, hp⟩
  have hR : condSet z topElem y = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro _; exact Set.mem_univ n
  · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩

theorem of_pos_not_zero {z x y : Pomega}
    (h0 : 0 ∉ z) (hp : ∃ k, k + 1 ∈ z) :
    dcondSet z x y = y := by
  have hL : condSet z x topElem = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inr ⟨Set.mem_univ n, hp⟩
  have hR : condSet z topElem y = y := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
      · exact (h0 hz).elim
      · exact hy
    · intro hy
      exact Or.inr ⟨hy, hp⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro hn
    rcases hn with ⟨_, hz⟩ | ⟨hy, _⟩
    · exact (h0 hz).elim
    · exact hy
  · intro hy
    exact Or.inr ⟨hy, hp⟩

theorem of_zero_not_pos {z x y : Pomega}
    (h0 : 0 ∈ z) (hp : ¬ ∃ k, k + 1 ∈ z) :
    dcondSet z x y = x := by
  have hL : condSet z x topElem = x := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨hx, _⟩ | ⟨_, ht⟩
      · exact hx
      · exact (hp ht).elim
    · intro hx
      exact Or.inl ⟨hx, h0⟩
  have hR : condSet z topElem y = topElem := by
    ext n
    constructor
    · intro _; exact Set.mem_univ n
    · intro _; exact Or.inl ⟨Set.mem_univ n, h0⟩
  rw [dcondSet, hL, hR]
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hx, _⟩ | ⟨_, ht⟩
    · exact hx
    · exact (hp ht).elim
  · intro hx
    exact Or.inl ⟨hx, h0⟩

theorem ofNat_one (x y : Pomega) : dcondSet (ofNat 1) x y = y := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

theorem ofNat_succ (n : ℕ) (x y : Pomega) :
    dcondSet (ofNat (n + 1)) x y = y :=
  dcondSet.of_pos_not_zero (by simp [ofNat]) ⟨n, by simp [ofNat]⟩

theorem ofNat_zero (x y : Pomega) : dcondSet (ofNat 0) x y = x := by
  ext n
  simp [dcondSet, condSet, ofNat, topElem]

theorem top (x y : Pomega) : dcondSet topElem x y = topElem := by
  ext n
  simp [dcondSet, condSet, topElem]

/-- Idempotence of `⊐ 0, 1` used for `bool`. -/
theorem bool_idem (u : Pomega) :
    dcondSet (dcondSet u (ofNat 0) (ofNat 1)) (ofNat 0) (ofNat 1) =
      dcondSet u (ofNat 0) (ofNat 1) := by
  rcases dcondSet.cases u with h | h | h | h
  · rw [dcondSet.of_zero_not_pos h.1 h.2, dcondSet.ofNat_zero]
  · rw [dcondSet.of_pos_not_zero h.1 h.2, dcondSet.ofNat_one]
  · rw [dcondSet.of_mixed h.1 h.2, dcondSet.top]
  · rw [dcondSet.of_empty h.1 h.2, dcondSet.bot]

end dcondSet

end DomainTheory.DataTypesAsLattices
