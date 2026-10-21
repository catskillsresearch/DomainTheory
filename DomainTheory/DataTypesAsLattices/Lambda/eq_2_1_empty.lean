/-ai
Scott 1976, (2.1). The maximal extension of ⊥ along a family p is the intersection of all the values p(n).

Membership through the empty clause is membership in every p(n). The numeral clause would require ⊥ to equal a numeral, and the residual clause would require ⊥ to be nonempty.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.1).** Maximal extension by cases. -/
theorem eq_2_1_empty (p : ℕ → Pomega) :
    maxExtend p botElem = ⋂ n, p n := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨_, hall⟩ | h | h
    · exact Set.mem_iInter.mpr hall
    · rcases h with ⟨n, hn, _⟩
      have : n ∈ (∅ : Pomega) := by
        have : (∅ : Pomega) = ofNat n := hn
        rw [this]; simp [ofNat]
      exact this.elim
    · exact (h.1 rfl).elim
  · intro hk
    exact Or.inl ⟨rfl, fun n => Set.mem_iInter.mp hk n⟩

end DomainTheory.DataTypesAsLattices
