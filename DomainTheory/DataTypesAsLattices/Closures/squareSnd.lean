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

def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}

namespace squareSnd

theorem bot : squareSnd botElem = botElem := by
  ext m
  simp [squareSnd, botElem]

theorem isScottContinuous : IsScottContinuous squareSnd := by
  constructor
  intro x
  ext m
  constructor
  · intro hm
    refine mem_scottUnion.mpr ⟨2 ^ (2 * m + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, squareSnd] using hm
    · simp [squareSnd, e_pow2]
  · intro hm
    obtain ⟨k, hk, hkm⟩ := mem_scottUnion.mp hm
    exact hk hkm

theorem top : squareSnd topElem = topElem := by
  ext m
  constructor
  · intro; exact Set.mem_univ m
  · intro; exact Set.mem_univ (2 * m + 1)

end squareSnd

end DomainTheory.DataTypesAsLattices
