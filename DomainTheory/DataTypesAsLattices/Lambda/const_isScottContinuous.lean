module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem const_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun _ : Pomega => c) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨0, by simp [e_zero], hk⟩
  · intro hk
    obtain ⟨_, _, hkn⟩ := mem_scottUnion.mp hk
    exact hkn

end DomainTheory.DataTypesAsLattices
