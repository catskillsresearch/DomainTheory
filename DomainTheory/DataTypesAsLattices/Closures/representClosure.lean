module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraicu2ecompact_finite_support
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
public import DomainTheory.DataTypesAsLattices.Continuous.scottUnion
public import Mathlib.Order.CompleteLattice.Defs

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def representClosure {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) : Pomega :=
  {m | D.compact m ≤ sSup (D.compact '' x)}

namespace representClosure

theorem mono {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) {x y : Pomega} (hxy : x ⊆ y) :
    representClosure D x ⊆ representClosure D y := by
  intro m hm
  exact hm.trans (by
    apply sSup_le
    intro q hq
    exact le_sSup (Set.image_mono hxy hq))

theorem isScottContinuous
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
    exact representClosure.mono D hnx hmn

theorem expansive {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    x ⊆ representClosure D x := by
  intro n hn
  exact le_sSup ⟨n, hn, rfl⟩

theorem idem {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    representClosure D (representClosure D x) = representClosure D x := by
  apply subset_antisymm
  · intro m hm
    exact hm.trans (by
      apply sSup_le
      intro q hq
      obtain ⟨n, hn, rfl⟩ := hq
      exact hn)
  · exact representClosure.expansive D (representClosure D x)

end representClosure

end DomainTheory.DataTypesAsLattices
