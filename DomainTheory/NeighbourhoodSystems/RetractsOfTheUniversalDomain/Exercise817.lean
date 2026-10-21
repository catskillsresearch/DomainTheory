/-ai
The neighbourhood system constructed in Exercise 8.12 is universal. The function space of the universal domain with itself embeds in the universal domain. The product of the universal domain with itself embeds in the universal domain. The sum of the universal domain with itself embeds in the universal domain.

The numbered name example_817 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.V_isUniversal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.funSpaceUU_trianglelefteq_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.prodUU_trianglelefteq_U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.sumUU_trianglelefteq_U

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
      (@DomainTheory.NeighbourhoodSystems.V_isUniversal.{u})
      DomainTheory.NeighbourhoodSystems.funSpaceUU_trianglelefteq_U)
    DomainTheory.NeighbourhoodSystems.prodUU_trianglelefteq_U)
  DomainTheory.NeighbourhoodSystems.sumUU_trianglelefteq_U

end DomainTheory.NeighbourhoodSystems
