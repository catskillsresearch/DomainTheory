module

public import DomainTheory.DataTypesAsLattices.FixedPoint.iterateBot
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.topRec
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

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
