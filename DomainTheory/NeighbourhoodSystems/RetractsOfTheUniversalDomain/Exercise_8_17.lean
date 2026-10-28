module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem exercise_8_17 :
    IsUniversal.{0} V ∧
      (prod U U ⊴ U) ∧
      (sum U U U_mem_nonempty U_mem_nonempty ⊴ U) ∧
      (funSpace U U ⊴ U) :=
  ⟨V.isUniversal, prodUU_trianglelefteq_U, sumUU_trianglelefteq_U, funSpaceUU_trianglelefteq_U⟩

end
