/-ai
Scott's Theorem 1.2 (ii) states that every u is contained in the graph of its application.

Every code is a pair of n and m, and that pair lies in the application at the basic element coded by n by reflexivity of inclusion, hence lies in the graph.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Continuous
public import DomainTheory.DataTypesAsLattices.Graph.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




/-- **Scott 1976, Theorem 1.2 (ii).** `u ⊆ graph(fun(u))`. -/
theorem theorem_1_2_ii (u : Pomega) : u ⊆ graph (funOf u) := by
  intro p hp
  obtain ⟨n, m, rfl⟩ := exists_pair p
  exact ⟨n, m, rfl, ⟨n, subset_rfl, hp⟩⟩

end DomainTheory.DataTypesAsLattices
