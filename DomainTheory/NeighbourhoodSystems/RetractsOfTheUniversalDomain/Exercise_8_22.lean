module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ExampleC_le_B

@[expose] public section

open DomainTheory.NeighbourhoodSystems

theorem example_822 : SeqDom.C ⊴ BitDom.B :=
  ExampleCLeB.C_trianglelefteq_B

