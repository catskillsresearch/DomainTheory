/-ai
If a binary operation is Scott continuous in each argument separately, then the least fixed point of its first-argument slice is Scott continuous in that argument.

Membership in the fixed point is membership in some bottom iterate. Continuity of that iterate in the parameter supplies a Scott-union witness, and the same iteration index makes it a witness for the union of the iterates. Conversely, a Scott-union witness and an iteration index, together with monotonicity of the continuous iterate, return the element to the fixed point.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.iterateBot_param_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem fix_param_isScottContinuous
    {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) :
    IsScottContinuous (fun x => fix (g x)) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    have := (iterateBot_param_isScottContinuous hgx hgy n).out x
    have : k ∈ scottUnion (fun z => iterateBot (g z) n) x := by
      rwa [← this]
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨m, hm, Set.mem_iUnion.mpr ⟨n, hkm⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hkm
    exact Set.mem_iUnion.mpr ⟨n,
      isScottContinuous_monotone (iterateBot_param_isScottContinuous hgx hgy n) hm hkn⟩

end DomainTheory.DataTypesAsLattices
