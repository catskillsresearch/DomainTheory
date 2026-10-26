module

public import DomainTheory.DataTypesAsLattices.Graph.IsGraph
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem iUnion_retract_isGraph {xs : ℕ → Pomega} (h : ∀ n, Retract (xs n)) :
    IsGraph (⋃ n, xs n) := by
  constructor
  intro k m n hkm hkn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hkm
  have hiG : IsGraph (xs i) := (theorem_1_2.iii (xs i)).mp (retract_isGraph (h i))
  exact Set.mem_iUnion.mpr ⟨i, hiG.out hi hkn⟩

end DomainTheory.DataTypesAsLattices
