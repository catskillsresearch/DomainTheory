module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.natPair

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NatPair

/-- Scott's Exercise 5.13: the Cantor pairing `num` with the three recurrence laws and
a two-sided inverse `unnum`. -/
theorem example_513 :
    num 0 0 = 0 ∧
    (∀ n m : ℕ, num n (m + 1) = num (n + 1) m + 1) ∧
    (∀ n : ℕ, num (n + 1) 0 = num 0 n + 1) ∧
    (∀ v : ℕ, numP (unnum v) = v) ∧
    (∀ c : ℕ × ℕ, unnum (numP c) = c) :=
  ⟨num_zero_zero, num_succ_right, num_succ_left, numP_unnum, unnum_numP⟩

