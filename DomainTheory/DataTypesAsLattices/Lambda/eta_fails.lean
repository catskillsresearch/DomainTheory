module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.IsGraph
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.e_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Table 1 (η) fails.** Not every element is a graph. -/
theorem eta_fails : ∃ u, graph (funOf u) ≠ u := by
  refine ⟨{pair 1 0}, ?_⟩
  intro h
  have hG : IsGraph {pair 1 0} := (theorem_1_2.iii _).mp h
  have hsub : e 1 ⊆ e 3 := by
    intro k hk
    have : k = 0 := by
      simpa [e_one] using hk
    subst this
    decide
  have : pair 3 0 ∈ ({pair 1 0} : Pomega) :=
    hG.out (by simp) hsub
  have : pair 3 0 = pair 1 0 := this
  exact (by simp [pair] : pair 3 0 ≠ pair 1 0) this

end DomainTheory.DataTypesAsLattices
