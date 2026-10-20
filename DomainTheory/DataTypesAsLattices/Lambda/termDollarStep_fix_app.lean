module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_iUnion
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_eq_iUnion_lt
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_iterate

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStep_fix_app (u z : Pomega) :
    funOf (funOf (fix termDollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix termDollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot termDollarStep n) u) z := by
    simp [fix, funOf_iUnion]
  rw [this, seqFun_eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [termDollarStep_iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [termDollarStep_iterate] using hn⟩

end DomainTheory.DataTypesAsLattices
