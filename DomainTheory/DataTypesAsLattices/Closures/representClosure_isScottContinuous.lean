module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_mono

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem representClosure_isScottContinuous
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) :
    IsScottContinuous (representClosure D) := by
  constructor
  intro x
  ext m
  constructor
  · intro hm
    obtain ⟨t, htx, hmt⟩ := D.compact_finite_support hm
    obtain ⟨n, hn⟩ := exists_code t
    refine mem_scottUnion.mpr ⟨n, ?_, ?_⟩
    · rw [hn]
      exact htx
    · change D.compact m ≤ sSup (D.compact '' e n)
      rwa [hn]
  · intro hm
    obtain ⟨n, hnx, hmn⟩ := mem_scottUnion.mp hm
    exact representClosure_mono D hnx hmn

end DomainTheory.DataTypesAsLattices
