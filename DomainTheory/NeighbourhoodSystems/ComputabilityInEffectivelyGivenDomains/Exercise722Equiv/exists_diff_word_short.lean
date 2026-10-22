module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.diffNFA_mem_accepts_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


/-- **The shortest witness of `denote e₁ ⊄ denote e₂`, if any, is short.** Generic
`exists_accepted_word_short` applied to `diffNFA`. -/
theorem exists_diff_word_short {e1 e2 : SExpr} (h : ¬ denote e1 ⊆ denote e2) :
    ∃ w, w.length < Fintype.card (Finset (autState e1) × Finset (autState e2)) ∧
      w ∈ denote e1 ∧ w ∉ denote e2 := by
  rw [Set.not_subset] at h
  have hne : (diffNFA e1 e2).accepts.Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := h
    exact ⟨x, (diffNFA_mem_accepts_iff e1 e2 x).mpr ⟨hx1, hx2⟩⟩
  obtain ⟨w, hlen, hmem⟩ := exists_accepted_word_short hne
  exact ⟨w, hlen, (diffNFA_mem_accepts_iff e1 e2 w).mp hmem⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
