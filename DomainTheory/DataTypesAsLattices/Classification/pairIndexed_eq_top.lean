
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.pairIndexed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem pairIndexed_eq_top (fs : ℕ → Pomega → Pomega) (x : Pomega) :
    pairIndexed fs x = topElem ↔ ∀ n, fs n x = topElem := by
  constructor
  · intro h n
    ext m
    constructor
    · intro _; trivial
    · intro _
      have : pair n m ∈ pairIndexed fs x := by rw [h]; exact Set.mem_univ _
      obtain ⟨n', m', heq, hm⟩ := this
      obtain ⟨rfl, rfl⟩ := pair_inj heq
      exact hm
  · intro h
    ext k
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨n, m, hk⟩ := exists_pair k
      exact ⟨n, m, hk.symm, by rw [h n]; exact Set.mem_univ m⟩

end DomainTheory.DataTypesAsLattices
