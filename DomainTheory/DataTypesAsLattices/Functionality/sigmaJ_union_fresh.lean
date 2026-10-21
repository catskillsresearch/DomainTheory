/-ai
If no code of a pair (j, k) lies in u, then σ_j of the union of u with the singleton of the code of (j, m) is the singleton of the code of (j, m + 1).

Commute the union, then use extensionality. A witness from the singleton forces the index m and the successor code. A witness from u contradicts freshness. The successor code is recovered from the singleton at the index m.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sigmaJ_union_fresh {j m : ℕ} {u : Pomega}
    (hu : ∀ k, pair j k ∉ u) :
    sigmaJ j (u ∪ {pair j m}) = ({pair j (m + 1)} : Pomega) := by
  rw [show u ∪ {pair j m} = ({pair j m} : Pomega) ∪ u by
    exact Set.union_comm _ _]
  ext p
  constructor
  · intro ⟨k, hp, hk⟩
    rcases hk with hk | hk
    · have hkm : k = m := (pair_inj hk).2
      subst k
      simpa using hp.symm
    · exact (hu k hk).elim
  · intro hp
    exact ⟨m, hp.symm, Or.inl (by simp)⟩

end DomainTheory.DataTypesAsLattices
