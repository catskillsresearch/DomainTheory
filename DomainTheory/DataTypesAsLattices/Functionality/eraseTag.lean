module

public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Z

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def eraseTag (j : ℕ) (u : Pomega) : Pomega :=
  {p | p ∈ u ∧ ∀ k, p ≠ pair j k}

namespace eraseTag

theorem Z_finite (p q m : ℕ) :
    eraseTag (max p q + 1) (Z m (e p) (e q)) = Z m (e p) (e q) := by
  ext k
  constructor
  · exact fun hk => hk.1
  · intro hk
    exact ⟨hk, fun r hkr => Z.finite_no_tag p q m r (hkr ▸ hk)⟩

theorem Z_finite_union (p q m : ℕ) :
    eraseTag (max p q + 1)
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z m (e p) (e q) := by
  ext k
  constructor
  · intro ⟨hk, hnot⟩
    rcases hk with hk | hk
    · exact hk
    · exact (hnot m (by simpa using hk)).elim
  · intro hk
    exact ⟨Or.inl hk, fun r hkr => Z.finite_no_tag p q m r (hkr ▸ hk)⟩

end eraseTag

end DomainTheory.DataTypesAsLattices
