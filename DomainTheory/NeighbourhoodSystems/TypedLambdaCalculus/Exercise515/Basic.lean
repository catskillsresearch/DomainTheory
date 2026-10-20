module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.star
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.G
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkA
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.parkY
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise515.kpow_succ

@[expose] public section

/-!
# Exercise 5.15 (Scott 1981, PRG-19, Lecture V) — free-semigroup powerset and Arden's lemma

> (For algebraists.) Regard `⟨{0,1}*, Λ, ·⟩` as the free semigroup on two generators. The powerset
> `P{0,1}*` is a domain (Exercise 4.17). For a word `e` set `e* = {Λ, e, e², …}`.
>
> (1) The least fixed point of `z = {e}·z ∪ {e'}` is `z = e*·{e'}`.
> (2) (David Park) The least solution of
> `x = a·x ∪ b·y ∪ c`, `y = b·x ∪ a·y ∪ d`
> is `x = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`, where `z* = Λ ∪ z*·z`.

Following Exercise 4.17, the powerset domain `P S` of a monoid `S` is the complete lattice
`(Set S, ⊆)` with pointwise product `s·t = {u·v ∣ u ∈ s, v ∈ t}` (`Set.mul`, `open Pointwise`).
Both parts are facts about the **Kleene algebra** `(Set S, ∪, ·, ∅, {1})` and hold for *any* monoid;
we prove them with `S` a general `Monoid` and specialise part (1) to `S = FreeMonoid Bool = {0,1}*`.

## Choice discipline

Mathlib's `Set`-level multiplicative lemmas (`mul_assoc`, `Set.union_mul`, `Set.mul_union`,
`Set.singleton_mul_singleton`), the order lemmas `Set.subset_iUnion`/`Set.iUnion_subset`, `Set`-power
(`pow_succ'`), `Submonoid.mem_powers_iff`, and `Monotone` over `Set` all depend on `Classical.choice`
in this toolchain (they route through `Set.image2`/`CompleteLattice` choice-using machinery). Every
*membership* iff (`Set.mem_mul`, `Set.mem_union`, `Set.mem_one`, `Set.mem_singleton_iff`) and every
*element-level* monoid lemma is choice-free. So we reprove the small slice of Kleene algebra we need
(`smul_assoc`, `sunion_mul`, `smul_union`) at the membership level, define `star` by an explicit
recursion (`kpow`) rather than `⋃ₙ zⁿ`, and phrase Arden's lemma without `Monotone` — keeping
everything **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-! ### A choice-free slice of Kleene algebra on `Set S` -/

/-! ### The star `z* = ⋃ₙ zⁿ`, by explicit recursion -/




/-! ### Arden's lemma -/


/-! ### Part (1): the single equation `z = {e}·z ∪ {e'}` -/

/-! ### Part (2): David Park's simultaneous system -/




end DomainTheory.NeighbourhoodSystems.Exercise515
