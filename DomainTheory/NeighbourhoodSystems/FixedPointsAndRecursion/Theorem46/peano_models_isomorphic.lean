module

public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.exists_unique_right
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.exists_unique_left

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Theorem 4.6 (Scott 1981, PRG-19).** *All models of Peano's Axioms are isomorphic.* Between
any two models there is a bijection `e : N ≃ M` of the underlying sets that preserves the
structure: `e 0 = □` and `e (n⁺) = (e n)#`. The bijection is the least-fixed-point relation
`Graph`, which `exists_unique_right`/`exists_unique_left` show is a one-one correspondence; the
two structure equations are the constructors `Graph.base`/`Graph.step`. -/
theorem peano_models_isomorphic (P : PeanoModel M) (Q : PeanoModel N) :
    ∃ e : M ≃ N, e P.zero = Q.zero ∧ ∀ m, e (P.succ m) = Q.succ (e m) := by
  classical
  refine ⟨⟨fun m => (exists_unique_right P Q m).choose,
          fun n => (exists_unique_left P Q n).choose, ?_, ?_⟩, ?_, ?_⟩
  · -- left inverse `g ∘ f = id`
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_left P Q _).choose_spec.2 m hf).symm
  · -- right inverse `f ∘ g = id`
    intro n
    have hg : Graph P Q (exists_unique_left P Q n).choose n :=
      (exists_unique_left P Q n).choose_spec.1
    exact ((exists_unique_right P Q _).choose_spec.2 n hg).symm
  · -- `f 0 = □`
    exact ((exists_unique_right P Q P.zero).choose_spec.2 Q.zero Graph.base).symm
  · -- `f (n⁺) = (f n)#`
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_right P Q (P.succ m)).choose_spec.2 _ (Graph.step hf)).symm

end PeanoModel
end DomainTheory.NeighbourhoodSystems
