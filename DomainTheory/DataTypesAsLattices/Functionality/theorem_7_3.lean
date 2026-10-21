/-ai
Scott 1976, Theorem 7.3, the functionality theorem. The combinator I lies in every function space A → A, K lies in every function space A → (B → A), and S lies in every function space (A → (B → C)) → ((A → B) → (A → C)). Any combinator with the functionality of I equals I, any combinator with the functionality of K equals K, and any combinator with the functionality of S that is extensional in its first argument and whose application is extensional in the second argument equals S.

The six conjuncts are the three functionality lemmas and the three uniqueness lemmas.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_3_i
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_3_ii
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_3_iii
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_3_I_unique
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_3_K_unique
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_3_S_unique

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 7.3 (The functionality theorem).** -/
theorem theorem_7_3 :
    (∀ A, (arrowE A A).mem Icomb) ∧
      (∀ A B, (arrowE A (arrowE B A)).mem Kcomb) ∧
      (∀ A B C,
        (arrowE (arrowE A (arrowE B C))
          (arrowE (arrowE A B) (arrowE A C))).mem Scomb) ∧
      (∀ i, (∀ A, (arrowE A A).mem i) → i = Icomb) ∧
      (∀ k, (∀ A B, (arrowE A (arrowE B A)).mem k) → k = Kcomb) ∧
      (∀ s,
        (∀ f, funOf s f =
          funOf s (graph (fun x => graph (fun y => funOf (funOf f x) y)))) →
        (∀ f g, funOf (funOf s f) g =
          funOf (funOf s f) (graph (fun x => funOf g x))) →
        (∀ A B C,
          (arrowE (arrowE A (arrowE B C))
            (arrowE (arrowE A B) (arrowE A C))).mem s) →
        s = Scomb) :=
  ⟨theorem_7_3_i, theorem_7_3_ii, theorem_7_3_iii,
    theorem_7_3_I_unique, theorem_7_3_K_unique, theorem_7_3_S_unique⟩

end DomainTheory.DataTypesAsLattices
