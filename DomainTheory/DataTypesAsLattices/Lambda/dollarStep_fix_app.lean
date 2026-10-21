/-ai
Applying the least fixed point of the dollar step to u and then to z yields the sequence revaluation of u at z.

The fixed point is the union of the iterates from ⊥, and application preserves that union, so the double application is the union of the double applications of the iterates. Sequence revaluation is the union of its finite stages, and each iterate agrees with the stage of the same index.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_iUnion
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_iterate
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_eq_iUnion_lt

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











































theorem dollarStep_fix_app (u z : Pomega) :
    funOf (funOf (fix dollarStep) u) z = seqFun u z := by
  have : funOf (funOf (fix dollarStep) u) z =
      ⋃ n, funOf (funOf (iterateBot dollarStep n) u) z := by
    simp [fix, funOf_iUnion]
  rw [this, seqFun_eq_iUnion_lt]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [dollarStep_iterate] using hn⟩
  · intro hk
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, by simpa [dollarStep_iterate] using hn⟩

end DomainTheory.DataTypesAsLattices
