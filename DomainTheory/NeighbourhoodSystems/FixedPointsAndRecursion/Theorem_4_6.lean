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

theorem theorem_46 :
    ∀ {M N : Type*} (P : PeanoModel M) (Q : PeanoModel N),
      ∃ e : M ≃ N, e P.zero = Q.zero ∧ ∀ m, e (P.succ m) = Q.succ (e m) :=
  @peano_models_isomorphic

end DomainTheory.NeighbourhoodSystems.PeanoModel
end
