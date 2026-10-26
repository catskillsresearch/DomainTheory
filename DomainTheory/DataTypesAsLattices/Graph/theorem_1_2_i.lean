
module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.IsGraph
public import DomainTheory.DataTypesAsLattices.Graph.lam
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 1.2 (i).** `fun(graph(f)) = f` when `f` is continuous. -/
theorem theorem_1_2_i {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (graph f) = f := by
  funext x
  ext m
  constructor
  · intro ⟨n, hn, hp⟩
    obtain ⟨n', m', heq, hm'⟩ := hp
    obtain ⟨rfl, rfl⟩ := pair_inj heq
    exact IsScottContinuous.monotone hf hn hm'
  · intro hm
    have : m ∈ scottUnion f x := by
      rw [← hf.out x]; exact hm
    obtain ⟨n, hn, hmn⟩ := mem_scottUnion.mp this
    exact ⟨n, hn, ⟨n, m, rfl, hmn⟩⟩

end DomainTheory.DataTypesAsLattices
