module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Definition_4_5

public import Mathlib.Algebra.Group.End

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
universe u v
namespace PeanoModel
variable {M : Type u} {N : Type v}

theorem peano_models_isomorphic (P : PeanoModel M) (Q : PeanoModel N) :
    ∃ e : M ≃ N, e P.zero = Q.zero ∧ ∀ m, e (P.succ m) = Q.succ (e m) := by
  classical
  refine ⟨⟨fun m => (exists_unique_right P Q m).choose,
          fun n => (exists_unique_left P Q n).choose, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_left P Q _).choose_spec.2 m hf).symm
  ·
    intro n
    have hg : Graph P Q (exists_unique_left P Q n).choose n :=
      (exists_unique_left P Q n).choose_spec.1
    exact ((exists_unique_right P Q _).choose_spec.2 n hg).symm
  ·
    exact ((exists_unique_right P Q P.zero).choose_spec.2 Q.zero Graph.base).symm
  ·
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_right P Q (P.succ m)).choose_spec.2 _ (Graph.step hf)).symm

end PeanoModel
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.PeanoModel
section
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
end

end DomainTheory.NeighbourhoodSystems.PeanoModel
end
