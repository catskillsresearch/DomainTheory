module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_subset_zero_one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

/-- **Example 8.4's two-point system `O = {{0},{0,1}}`.** Tokens `Δ = {0,1} : Fin 2`; the only
neighbourhoods are `{0}` (most informative) and `{0,1}` (the master, least informative). -/
def O : NeighborhoodSystem (Fin 2) where
  mem X := X = ({0} : Set (Fin 2)) ∨ X = ({0, 1} : Set (Fin 2))
  master := ({0, 1} : Set (Fin 2))
  master_nonempty := ⟨0, by simp⟩
  master_mem := Or.inr rfl
  inter_mem := by
    rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
    · exact Or.inl (Set.inter_self _)
    · exact Or.inl (Set.inter_eq_left.mpr fin2_zero_subset_zero_one)
    · exact Or.inl (Set.inter_eq_right.mpr fin2_zero_subset_zero_one)
    · exact Or.inr (Set.inter_self _)
  sub_master := by
    rintro X (rfl | rfl)
    · exact fin2_zero_subset_zero_one
    · exact subset_rfl

end DomainTheory.NeighbourhoodSystems
