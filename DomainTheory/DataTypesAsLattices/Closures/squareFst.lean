module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}

namespace squareFst

theorem bot : squareFst botElem = botElem := by
  ext n
  simp [squareFst, botElem]

theorem isScottContinuous : IsScottContinuous squareFst := by
  constructor
  intro x
  ext n
  constructor
  · intro hn
    refine mem_scottUnion.mpr ⟨2 ^ (2 * n), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareFst] using hn
    · simp [squareFst, e_pow2]
  · intro hn
    obtain ⟨m, hm, hnm⟩ := mem_scottUnion.mp hn
    exact hm hnm

theorem top : squareFst topElem = topElem := by
  ext n
  constructor
  · intro; exact Set.mem_univ n
  · intro; exact Set.mem_univ (2 * n)

end squareFst

end DomainTheory.DataTypesAsLattices
