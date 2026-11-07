module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ExampleC_le_B

@[expose] public section

open DomainTheory.NeighbourhoodSystems

theorem exercise_8_22 : SeqDom.C ⊴ BitDom.B :=
  Exercise822.C_trianglelefteq_B

end
