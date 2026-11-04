module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Retracts.graphLemmas
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Pomega.pair

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace funOf

theorem ext_graph {f g : Pomega}
    (hf : f = graph (fun x => funOf f x))
    (hg : g = graph (fun x => funOf g x))
    (h : ∀ x, funOf f x = funOf g x) : f = g := by
  rw [hf, hg]
  exact graph_ext h

theorem top (x : Pomega) : funOf topElem x = topElem := by
  ext m
  constructor
  · intro
    trivial
  · intro
    exact ⟨0, by simp [e.zero], trivial⟩

theorem condSet (z x y w : Pomega) :
    funOf (DomainTheory.DataTypesAsLattices.condSet z x y) w =
      DomainTheory.DataTypesAsLattices.condSet z (funOf x w) (funOf y w) := by
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    rcases hp with ⟨hx, h0⟩ | ⟨hy, ht⟩
    · exact Or.inl ⟨⟨n, hn, hx⟩, h0⟩
    · exact Or.inr ⟨⟨n, hn, hy⟩, ht⟩
  · intro hm
    rcases hm with ⟨⟨n, hn, hx⟩, h0⟩ | ⟨⟨n, hn, hy⟩, ht⟩
    · exact ⟨n, hn, Or.inl ⟨hx, h0⟩⟩
    · exact ⟨n, hn, Or.inr ⟨hy, ht⟩⟩

theorem dcondSet (z x y w : Pomega) :
    funOf (DomainTheory.DataTypesAsLattices.dcondSet z x y) w =
      DomainTheory.DataTypesAsLattices.dcondSet z (funOf x w) (funOf y w) := by
  simp only [DomainTheory.DataTypesAsLattices.dcondSet]
  rw [condSet, condSet, condSet, top]

theorem e_union_fresh (p j m : ℕ) (u : Pomega) (hpj : p < j) :
    funOf (e p) (u ∪ {pair j m}) = funOf (e p) u := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨r, hr, hprk⟩ := hk
    refine ⟨r, ?_, hprk⟩
    intro t ht
    rcases hr ht with htu | htag
    · exact htu
    · have htEq : t = pair j m := by simpa using htag
      have hjr : j ≤ r := by
        rw [htEq] at ht
        exact (pair_le_left j m).trans (e.mem_le ht)
      have hrp : r ≤ p := (pair_le_left r k).trans (e.mem_le hprk)
      exact (Nat.not_lt_of_ge (hjr.trans hrp) hpj).elim
  · exact monotone_right (e p) Set.subset_union_left

end funOf

end DomainTheory.DataTypesAsLattices
