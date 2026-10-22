module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eraseTag_Z_finite_union (p q m : ℕ) :
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
    exact ⟨Or.inl hk, fun r hkr => Z_finite_no_tag p q m r (hkr ▸ hk)⟩

end DomainTheory.DataTypesAsLattices
