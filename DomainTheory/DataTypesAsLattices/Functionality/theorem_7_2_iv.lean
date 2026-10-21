/-ai
Scott 1976, Theorem 7.2 (iv). For retracts a and b, relatedness in E of a ⊕ b agrees with relatedness in the sum of E_a and E_b, or with both elements being bottom, or with both elements being top.

A related pair in E of the sum is one element of the sum repeated. The range characterization splits it into bottom, top, a left injection, or a right injection. The extreme cases are the two added pairs. An injection is rewritten as a pair element, and the payload relation is the identity relation of E_a or of E_b. Conversely, a summand gives equal payloads and therefore equal elements, and the left or right typing lemmas place them in the sum. The pair of bottoms and the pair of tops are typed by the bottom and top lemmas.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem_eq_pairSeq
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_bot
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inl
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_inr
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_top
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_iff

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 7.2 (iv).**
The exact identity
`E_{a ⊕ b} = E_a + E_b ∪ {⟨⊥,⊥⟩, ⟨⊤,⊤⟩}`. -/
theorem theorem_7_2_iv {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b)
    (u v : Pomega) :
    (Ea (plusR a b)).rel u v ↔
      (sumE (Ea a) (Ea b)).rel u v ∨
        (u = botElem ∧ v = botElem) ∨ (u = topElem ∧ v = topElem) := by
  constructor
  · intro huv
    rcases huv with ⟨hu, hv, huv⟩
    subst v
    rcases (plusR_typed_iff ha hb).mp hu with
      rfl | rfl | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by simpa [pairSeq_app_one] using (show (Ea a).rel x x from ⟨hx, hx, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by rw [pairElem_eq_pairSeq, pairSeq_app_one],
          by simpa [pairSeq_app_one] using (show (Ea b).rel y y from ⟨hy, hy, rfl⟩)⟩)
  · intro h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    rcases h with ⟨hu, hv, hA⟩ | ⟨hu, hv, hB⟩
    · rcases hA with ⟨hxt, hyt, heq⟩
      have heq' : u = v := by
        rw [hu, hv, heq]
      refine ⟨?_, ?_, heq'⟩
      · rw [hu]; exact plusR_typed_inl hxt
      · rw [hv]; exact plusR_typed_inl hyt
    · rcases hB with ⟨hxt, hyt, heq⟩
      have heq' : u = v := by
        rw [hu, hv, heq]
      refine ⟨?_, ?_, heq'⟩
      · rw [hu]; exact plusR_typed_inr hxt
      · rw [hv]; exact plusR_typed_inr hyt
    · exact ⟨plusR_typed_bot a b, plusR_typed_bot a b, rfl⟩
    · exact ⟨plusR_typed_top a b, plusR_typed_top a b, rfl⟩

end DomainTheory.DataTypesAsLattices
