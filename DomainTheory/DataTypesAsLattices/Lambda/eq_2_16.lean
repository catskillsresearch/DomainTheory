/-ai
The least fixed point of x ↦ {0} ∪ (x + 1) is ⊤.

Every number k lies in the (k + 1)-st iterate from ⊥: 0 lies in the first iterate, and if n lies in the (n + 1)-st iterate then n + 1 lies in the next by the successor clause. The least fixed point is the union of the iterates, and every element of that union lies in ⊤.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eq_2_16 : fix topRec = topElem := by
  apply subset_antisymm
  · intro k _; trivial
  · intro k _
    have hiter : ∀ n, n ∈ iterateBot topRec (n + 1) := by
      intro n
      induction n with
      | zero => simp [iterateBot, topRec, ofNat]
      | succ n ih =>
        refine Or.inr ⟨n, ?_, rfl⟩
        simpa [iterateBot] using ih
    exact Set.mem_iUnion.mpr ⟨k + 1, hiter k⟩

end DomainTheory.DataTypesAsLattices
