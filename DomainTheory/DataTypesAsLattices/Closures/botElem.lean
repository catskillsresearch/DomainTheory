module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace botElem

theorem ne_top : (topElem : Pomega) ≠ botElem := by
  intro h
  have h0 : (0 : ℕ) ∈ (botElem : Pomega) := h ▸ Set.mem_univ 0
  simp [botElem] at h0

theorem exists_mem {x : Pomega} (h : x ≠ botElem) : ∃ m, m ∈ x := by
  by_contra hc
  refine h ?_
  ext n
  simp only [mem_botElem, iff_false]
  exact fun hn => hc ⟨n, hn⟩

theorem union_empty (x : Pomega) : x ∪ botElem = x := Set.union_empty x

theorem empty_union (x : Pomega) : botElem ∪ x = x := Set.empty_union x

end botElem

end DomainTheory.DataTypesAsLattices
