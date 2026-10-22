/-ai
A Scott continuous map is monotone for inclusion: if x is contained in y, then f(x) is contained in f(y).

If m lies in f(x), the membership characterization of the Scott union supplies a finite code whose finite set is contained in x and whose f-value contains m. That finite set is still contained in y, so m lies in f(y).
ai-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order
public import DomainTheory.DataTypesAsLattices.Pomega
public import DomainTheory.DataTypesAsLattices.Continuous.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace


theorem isScottContinuous_monotone {f : Pomega → Pomega}
    (hf : IsScottContinuous f) {x y : Pomega} (h : x ⊆ y) : f x ⊆ f y := by
  intro m hm
  rw [hf x, mem_scottUnion] at hm
  rw [hf y, mem_scottUnion]
  obtain ⟨n, hn, hmn⟩ := hm
  exact ⟨n, subset_trans hn h, hmn⟩

end DomainTheory.DataTypesAsLattices
