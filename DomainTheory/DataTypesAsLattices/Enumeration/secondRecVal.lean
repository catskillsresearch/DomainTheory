
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.num
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def secondRecVal (u : Pomega) : Pomega :=
  graph (fun x => ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))))

namespace secondRecVal

theorem isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x =>
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m)))) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    exact mem_scottUnion.mpr ⟨2 ^ m, by simp [e_pow2, Set.singleton_subset_iff, hm],
      Set.mem_iUnion₂.mpr ⟨m, by simp [e_pow2], hkm⟩⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hkn
    exact Set.mem_iUnion₂.mpr ⟨m, hn hm, hkm⟩

theorem app (u x : Pomega) :
    funOf (secondRecVal u) x =
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m))) :=
  beta (secondRecVal.isScottContinuous u) x

end secondRecVal

end DomainTheory.DataTypesAsLattices
