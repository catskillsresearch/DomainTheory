/-ai
A union of retracts is a graph: if a pair lies in the union and the finite-set index is enlarged, the new pair still lies in the union.

The original pair lies in some summand. That summand is a graph, because a retract is a graph and Theorem 1.2(iii) turns the graph property into this closure. The enlarged index therefore remains in the same summand, and hence in the union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.retract_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem iUnion_retract_isGraph {xs : ℕ → Pomega} (h : ∀ n, IsRetract (xs n)) :
    IsGraph (⋃ n, xs n) := by
  intro k m n hkm hkn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hkm
  have hiG : IsGraph (xs i) := (theorem_1_2_iii (xs i)).mp (retract_isGraph (h i))
  exact Set.mem_iUnion.mpr ⟨i, hiG hi hkn⟩

end DomainTheory.DataTypesAsLattices
