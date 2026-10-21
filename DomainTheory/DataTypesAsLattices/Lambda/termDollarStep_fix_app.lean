/-ai
Applying the least fixed point of the term-level dollar step first to u and then to z equals the sequence revaluation of u at z.

The fixed point is the directed union of the iterates from bottom, and application preserves that union, so the left-hand side is the union over n of the double application of the n-th iterate. The sequence revaluation is the union of its finite stages. Extensionality identifies the two unions because the iterate theorem equates each double application with the corresponding finite stage.
ai-/
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
