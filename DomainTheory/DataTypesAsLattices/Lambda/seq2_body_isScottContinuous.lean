module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem seq2_body_isScottContinuous (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x (condSet (predSet z) y botElem)) := by
  constructor
  intro z
  have H := theorem_1_3_diag (x := z)
    (f := fun z w => condSet z x (condSet (predSet w) y botElem))
    (fun _w => condSet_isScottContinuous_left x _)
    (fun _z =>
      theorem_1_3 (condSet_isScottContinuous_right _z x)
        (theorem_1_3 (condSet_isScottContinuous_left y botElem)
          predSet_isScottContinuous))
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} := by
      rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this

end DomainTheory.DataTypesAsLattices
