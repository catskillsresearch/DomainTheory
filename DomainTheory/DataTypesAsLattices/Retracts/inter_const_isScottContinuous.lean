module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem inter_const_isScottContinuous {f : Pomega → Pomega}
    (hf : IsScottContinuous f) (b : Pomega) :
    IsScottContinuous (fun z => f z ∩ b) := by
  constructor
  intro x
  ext k
  constructor
  · intro ⟨hkf, hkb⟩
    have : k ∈ scottUnion f x := by rwa [← hf.out x]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
  · intro hk
    obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
    exact ⟨IsScottContinuous.monotone hf hn hkn, hkb⟩

end DomainTheory.DataTypesAsLattices
