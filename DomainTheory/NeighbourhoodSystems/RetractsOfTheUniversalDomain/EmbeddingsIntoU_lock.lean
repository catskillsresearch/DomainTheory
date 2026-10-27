module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_817.{u} : And
  (And
    (And (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U))
    (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Sum.{0, 0} Rat Rat) Rat
      (@DomainTheory.NeighbourhoodSystems.prod.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
      DomainTheory.NeighbourhoodSystems.U))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Option.{0} (Sum.{0, 0} Rat Rat)) Rat
    (@DomainTheory.NeighbourhoodSystems.sum.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U_mem_nonempty
      DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
    DomainTheory.NeighbourhoodSystems.U) :=
  @And.intro
  (And
    (And (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U))
    (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Sum.{0, 0} Rat Rat) Rat
      (@DomainTheory.NeighbourhoodSystems.prod.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
      DomainTheory.NeighbourhoodSystems.U))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Option.{0} (Sum.{0, 0} Rat Rat)) Rat
    (@DomainTheory.NeighbourhoodSystems.sum.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
      DomainTheory.NeighbourhoodSystems.U DomainTheory.NeighbourhoodSystems.U_mem_nonempty
      DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
    DomainTheory.NeighbourhoodSystems.U)
  (@And.intro
    (And (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U))
    (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0} (Sum.{0, 0} Rat Rat) Rat
      (@DomainTheory.NeighbourhoodSystems.prod.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U)
      DomainTheory.NeighbourhoodSystems.U)
    (@And.intro (@DomainTheory.NeighbourhoodSystems.IsUniversal.{u, 0} Nat DomainTheory.NeighbourhoodSystems.V)
      (@DomainTheory.NeighbourhoodSystems.Trianglelefteq.{0, 0}
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        Rat
        (@DomainTheory.NeighbourhoodSystems.funSpace.{0, 0} Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U)
        DomainTheory.NeighbourhoodSystems.U)
      (@DomainTheory.NeighbourhoodSystems.V.isUniversal.{u})
      DomainTheory.NeighbourhoodSystems.funSpaceUU_trianglelefteq_U)
    DomainTheory.NeighbourhoodSystems.prodUU_trianglelefteq_U)
  DomainTheory.NeighbourhoodSystems.sumUU_trianglelefteq_U


end DomainTheory.NeighbourhoodSystems
