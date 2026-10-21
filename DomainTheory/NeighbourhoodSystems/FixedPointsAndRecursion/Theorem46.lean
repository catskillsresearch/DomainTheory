/-ai
Any two models of Peano's axioms admit a bijection of their underlying types that sends zero to zero and commutes with the successor.

The numbered name theorem_46 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.peano_models_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.PeanoModel

set_option linter.unusedVariables false

theorem theorem_46.{u, v} : ∀ {M : Type u} {N : Type v} (P : DomainTheory.NeighbourhoodSystems.PeanoModel M)
  (Q : DomainTheory.NeighbourhoodSystems.PeanoModel N),
  ∃ (e : Equiv M N),
    And
      (@Eq N
        (@DFunLike.coe (Equiv M N) M (fun (x : M) => N)
          (@EquivLike.toFunLike (Equiv M N) M N (@Equiv.instEquivLike M N)) e
          (@DomainTheory.NeighbourhoodSystems.PeanoModel.zero M P))
        (@DomainTheory.NeighbourhoodSystems.PeanoModel.zero N Q))
      (∀ (m : M),
        @Eq N
          (@DFunLike.coe (Equiv M N) M (fun (x : M) => N)
            (@EquivLike.toFunLike (Equiv M N) M N (@Equiv.instEquivLike M N)) e
            (@DomainTheory.NeighbourhoodSystems.PeanoModel.succ M P m))
          (@DomainTheory.NeighbourhoodSystems.PeanoModel.succ N Q
            (@DFunLike.coe (Equiv M N) M (fun (x : M) => N)
              (@EquivLike.toFunLike (Equiv M N) M N (@Equiv.instEquivLike M N)) e m))) :=
  @DomainTheory.NeighbourhoodSystems.PeanoModel.peano_models_isomorphic

end DomainTheory.NeighbourhoodSystems.PeanoModel
