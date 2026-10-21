/-ai
The graph of the application of u equals u if and only if u is a graph.

If the two sets are equal and the pair of k and m lies in u with the basic element coded by k contained in the one coded by n, the same pair lies in the graph. Membership there supplies an equal pair and a membership in the application at the basic element coded by k. Injectivity of pairing aligns the components, and the finite witness inside that basic element remains inside the basic element coded by n, so the pair of n and m lies in the graph and therefore in u. Conversely, if u is a graph, one inclusion takes a pair in the graph of the application, whose membership witness is a pair in u at a smaller basic element, and the graph property enlarges it. The other inclusion is Theorem 1.2 (ii).
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic
public import DomainTheory.DataTypesAsLattices.Graph.mem_graph
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_ii

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





theorem theorem_1_2_iii (u : Pomega) :
    graph (funOf u) = u ↔ IsGraph u := by
  constructor
  · intro heqGraph k m n hkm hkn
    have hmem : pair k m ∈ graph (funOf u) := heqGraph.symm ▸ hkm
    rcases mem_graph.mp hmem with ⟨k', m', hp, hmfun⟩
    have hk : k = k' := (pair_inj hp).1
    have hm : m = m' := (pair_inj hp).2
    have hmfun' : m ∈ funOf u (e k) := by
      rw [hk, hm]; exact hmfun
    rcases hmfun' with ⟨j, hj, hpj⟩
    have hgraph : pair n m ∈ graph (funOf u) :=
      mem_graph.mpr ⟨n, m, rfl, ⟨j, subset_trans hj hkn, hpj⟩⟩
    exact heqGraph ▸ hgraph
  · intro hu
    apply subset_antisymm
    · intro p hp
      rcases hp with ⟨n, m, rfl, ⟨k, hk, hkm⟩⟩
      exact hu hkm hk
    · exact theorem_1_2_ii u

end DomainTheory.DataTypesAsLattices
