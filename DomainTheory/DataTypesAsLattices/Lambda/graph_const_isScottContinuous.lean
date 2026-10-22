/-ai
If a binary operation is Scott continuous in its first argument, then the graph of its second-argument slice is Scott continuous in the first argument.

A code in the graph means the value lies in the corresponding slice. Continuity of that slice supplies a Scott-union witness, which is a witness for the graph. Conversely, monotonicity of the continuous slice returns the code from a Scott-union witness to the graph.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- `graph (fun y => g x y)` is continuous in `x` when `g` is continuous in `x`. -/
theorem graph_const_isScottContinuous
    (g : Pomega → Pomega → Pomega)
    (hg : ∀ y, IsScottContinuous (fun x => g x y)) :
    IsScottContinuous (fun x => graph (fun y => g x y)) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, m, rfl, hm⟩
    have : m ∈ scottUnion (fun z => g z (e n)) x := by
      rw [← (hg (e n)).out x]; exact hm
    obtain ⟨p, hp, hmp⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨p, hp, n, m, rfl, hmp⟩
  · intro hk
    obtain ⟨p, hp, n, m, rfl, hm⟩ := mem_scottUnion.mp hk
    exact ⟨n, m, rfl, isScottContinuous_monotone (hg (e n)) hp hm⟩

end DomainTheory.DataTypesAsLattices
