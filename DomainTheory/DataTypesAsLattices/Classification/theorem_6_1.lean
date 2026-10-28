
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.isScottOpen_isUpper
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottOpen
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.charOpen
public import DomainTheory.DataTypesAsLattices.Classification.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem theorem_6_1 :
    (∀ f : Pomega → Pomega, IsScottContinuous f →
        IsScottOpen {x | 0 ∈ f x}) ∧
      (∀ U, IsScottOpen U →
        ∃ f, IsScottContinuous f ∧ U = {x | 0 ∈ f x}) := by
  constructor
  · intro f hf
    refine ⟨{n | 0 ∈ f (e n)}, ?_⟩
    ext x
    constructor
    · intro hx
      have : 0 ∈ scottUnion f x := by rwa [← hf.out x]
      obtain ⟨n, hn, h0⟩ := mem_scottUnion.mp this
      exact Set.mem_iUnion₂.mpr ⟨n, h0, hn⟩
    · intro hx
      obtain ⟨n, h0, hn⟩ := Set.mem_iUnion₂.mp hx
      exact IsScottContinuous.monotone hf hn h0
  · intro U hU
    refine ⟨charOpen U, charOpen_isScottContinuous U, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨B, rfl⟩ := hU
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨rfl, n, hxn, ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, (subset_rfl : e n ⊆ e n)⟩
    · intro ⟨_, n, hn, hne⟩
      exact isScottOpen_isUpper hU hne hn

end DomainTheory.DataTypesAsLattices
