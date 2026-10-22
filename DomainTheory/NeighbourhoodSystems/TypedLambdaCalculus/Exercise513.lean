/-ai
This file gathers and re-exports the one-one pairing of Exercise 5.13. It re-exports the triangular numbers with their successor, product, comparison, and monotonicity laws, the pairing num with value zero at the origin and the two successor recurrences, the bound of a value by the next triangular number, and injectivity of the pairing. It also re-exports the diagonal step, the inverse decoding, the equivalence between pairs of natural numbers and natural numbers, transport of power-set domains along a bijection of index types, and the order isomorphisms among the power set of the natural numbers, the power set of pairs, and the product of two power sets.

The diagonal iterate inverts the pairing function: iterating the pairing value of a cell returns that cell.

The numbered name example_513 is that statement.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum_numP

@[expose] public section

/-!
# Exercise 5.13 (Scott 1981, PRG-19, Lecture V) — a one-one pairing `num : N × N → N`

> Prove the existence of a one-one function `num : ℕ × ℕ → ℕ` such that
>
> * `num(0, 0) = 0`,
> * `num(n, m+1) = num(n+1, m) + 1`,
> * `num(n+1, 0) = num(0, n) + 1`.
>
> Draw a picture (an infinite matrix) for the function and find a closed form for its values.
> Use the function to prove the isomorphism of the domains `P N`, `P(N × N)`, `P N × P N`.

## The picture

Reading `n` down the rows and `m` across the columns, the three recurrences walk the **anti-diagonals**
`n + m = const`, climbing one step (`+1`) each move and jumping to the start of the next diagonal at
the left edge:

```
        m=0   m=1   m=2   m=3
n=0      0     2     5     9
n=1      1     4     8
n=2      3     7
n=3      6
```

## The closed form

On the anti-diagonal `s = n + m` the values run `T(s), T(s)+1, …, T(s)+s` where `T(s) = s(s+1)/2`
is the `s`-th triangular number; the offset within the diagonal is exactly `m`. Hence

  `num n m = (n + m) * (n + m + 1) / 2 + m`

— the **Cantor pairing function**. We take this as the definition (`num`), verify Scott's three
recurrences (`num_zero_zero`, `num_succ_right`, `num_succ_left`), and prove it is one-one
(`num_injective`). In fact it is a *bijection*: we build a choice-free inverse `unnum` (iterate the
diagonal walk `nextCell` from `(0,0)`) and package the bijection as `numEquiv : ℕ × ℕ ≃ ℕ`.

## The domain isomorphisms

Following Exercise 4.17, the power-set domain `P A` is modelled by the complete lattice `(Set A, ⊆)`.
Order-isomorphisms of these domains are then induced by bijections of the index types
(`setCongr`). Since `ℕ × ℕ ≃ ℕ` (via `numEquiv`) and `ℕ ⊕ ℕ ≃ ℕ` (Mathlib's
`Equiv.natSumNatEquivNat`), all three domains are isomorphic:

  `P N ≅ P(N × N)`            (`PN_orderIso_PNN`),
  `P N ≅ P N × P N`          (`PN_orderIso_prod`),
  `P(N × N) ≅ P N × P N`     (`PNN_orderIso_prod`).

Everything (including `numEquiv` and the order-isomorphisms) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-! ### Triangular numbers -/


/-! ### The pairing function `num` -/


/-! ### The inverse: walking the diagonals -/


/-! ### The domain isomorphisms

The power-set domain `P A` is the complete lattice `(Set A, ⊆)` (Exercise 4.17). A bijection of
index types lifts to an order-isomorphism of power-set domains. -/

variable {α β : Type*}


end DomainTheory.NeighbourhoodSystems.Exercise513

namespace DomainTheory.NeighbourhoodSystems.Exercise513

set_option linter.unusedVariables false

theorem example_513 : ∀ (c : Prod Nat Nat),
  @Eq (Prod Nat Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise513.unnum (DomainTheory.NeighbourhoodSystems.Exercise513.numP c)) c :=
  DomainTheory.NeighbourhoodSystems.Exercise513.unnum_numP

end DomainTheory.NeighbourhoodSystems.Exercise513
