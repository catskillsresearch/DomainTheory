/-ai
This file gathers and re-exports the definitions of Exercise 4.21: Scott's operator on subsets of pairs of naturals, the order relation as such a subset, the successor image of a set of naturals, the up-set of numbers at least a given natural, the addition equivalence, and the multiplication operator. The module comment records that the order relation is the unique fixed point of the operator, that the unique function of 4.13(3) sending zero to all naturals and commuting with successor is the up-set function, that the unique isomorphism of the naturals with the up-set of m is addition by m, and that the least solution of the multiplication equation is the set of multiples.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.leRel
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.succImage
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.upSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.addIso
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.mulOp

@[expose] public section

/-!
# Exercise 4.21 (Scott 1981, PRG-19, Lecture IV) — `≤` as a unique fixed point; addition & multiplication

Scott asks to show that the **less-than-or-equal-to relation** `ℓ ⊆ ℕ × ℕ` is *uniquely* determined
by the fixed-point equation

  `ℓ = {(n, n) ∣ n ∈ ℕ} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}`.

Working in the power-set domain `P(ℕ × ℕ)` (a complete lattice, Exercise 4.14), the right-hand side
is a monotone operator `leOp`. We show:

* `leRel = {(n, m) ∣ n ≤ m}` solves the equation (`leRel_isFixed`);
* the solution is **unique** (`leOp_unique`): for *any* fixed point `u` one proves, by induction on
  the second coordinate, that `(n, m) ∈ u ↔ n ≤ m`. (Unlike a general least-fixed-point situation,
  here the equation pins the relation down completely, because the clause `(n, m⁺)` never produces a
  pair with second coordinate `0`.)

Scott then considers `⟨P ℕ, ℕ, ⁺⟩` with `x⁺ = {n⁺ ∣ n ∈ x}` and the **unique function**
`[·] : ℕ → P ℕ` of 4.13(3) determined by `[0] = ℕ` and `[m⁺] = [m]⁺`. We identify it as the up-set
`[m] = {k ∣ m ≤ k}` (`upSet`), with `upSet_zero`/`upSet_succ` the two recursion equations and
`upSet_unique` their uniqueness (4.13(3)).

The structures `⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` are **uniquely isomorphic** via `n ↦ m + n`
(`addIso`), connecting the isomorphism with **ordinary addition** (`addIso_apply`): the unique
structure-preserving bijection sends `n` to `m + n`.

Finally, **multiplication**: the hint equation `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` has, as its least
solution in `P ℕ`, exactly the set of multiples of `n` (`mulOp_lfp_eq_multiples`).

All set-level constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-! ### The order relation as a unique fixed point. -/


/-! ### The function `[·] : ℕ → P ℕ` of 4.13(3): the up-sets. -/


/-! ### The isomorphism `⟨ℕ, 0, ⁺⟩ ≅ ⟨[m], m, ⁺⟩` is addition. -/


/-! ### Multiplication via the hint fixed-point equation. -/

end DomainTheory.NeighbourhoodSystems.Exercise421
