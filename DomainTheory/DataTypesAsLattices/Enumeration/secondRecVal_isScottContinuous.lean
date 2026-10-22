/-ai
For every element u, the map sending x to the union over m in x of u applied to the numeral of apply(m)(num(m)) is Scott continuous.

An element of the union lies in one summand for some m in x, hence lies in the Scott union at the singleton of m, which is the power of two 2^m and sits below x. Conversely, an element of the Scott union lies in the union over some finite piece below x, and the witnessing index from that piece still belongs to x.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


theorem secondRecVal_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x =>
      ⋃ m ∈ x, funOf u (ofNat (applyNat m (num m)))) := by
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

end DomainTheory.DataTypesAsLattices
