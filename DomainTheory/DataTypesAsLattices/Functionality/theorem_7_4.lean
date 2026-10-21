/-ai
Scott 1976, Theorem 7.4, the iterator theorem. For every restricted equivalence A and every n, the iterator Z_n lies in the function space from A → A to A → A. Any combinator that is extensional in its function argument and lies in every such function space equals Z_n for some n.

The two conjuncts are the functionality lemma for the iterators and the uniqueness lemma for the iterators.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_i
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_unique

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























/-- **Scott 1976, Theorem 7.4 (The iterator theorem).**
The functionality is both satisfied by and globally characterizes the
iterators. -/
theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n :=
  ⟨theorem_7_4_i, theorem_7_4_unique⟩

end DomainTheory.DataTypesAsLattices
