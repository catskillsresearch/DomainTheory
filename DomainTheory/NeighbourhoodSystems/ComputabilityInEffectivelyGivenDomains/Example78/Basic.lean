/-ai
This file gathers and re-exports the ingredients of Example 7.8: the cofinite neighbourhoods, membership in them, the neighbourhood of index zero, their intersection law, injectivity of the enumeration, the powerset neighbourhood system, and its computable presentation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.PN
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.PNpres
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_injective

@[expose] public section

/-!
# Example 7.8 (Scott 1981, PRG-19, §7) — the powerset `PN` is effectively given

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Example 7.8.** We have often made reference to the powerset `PN` as a domain and we should
> check here that it is effectively given. … the neighbourhoods of `PN` are ordered … in the
> partial ordering *converse* to that [of finite sets]. … What we need first is an enumeration of
> all finite sets of integers:
> `Eₙ = {k ∣ ∃ i, j. i < 2ᵏ and n = i + 2ᵏ + j·2ᵏ⁺¹}`.
> The idea is that `k ∈ Eₙ` means the exponent `k` occurs in the binary expansion of `n`. … as a
> neighbourhood system `(PN) = {N ∖ Eₙ ∣ n ∈ ℕ}`. As the relationship `Eₙ ∪ Eₘ = E_k` is
> recursive, there is no trouble in proving that this is a computable presentation. In this system,
> of course, any two neighbourhoods are consistent.

**Formalisation.** Scott's `Eₙ = {k ∣ ∃ i,j. i < 2ᵏ ∧ n = i + 2ᵏ + j·2ᵏ⁺¹}` is exactly "`k` is a
set bit of `n`", i.e. `Nat.testBit n k`. The neighbourhoods are the *cofinite* sets
`ℕ ∖ Eₙ = {k ∣ ¬ n.testBit k}`, here `nbhd n := {k ∣ n.testBit k = false}` (so `nbhd 0 = ℕ = Δ`).

* `nbhd_inter`: `nbhd n ∩ nbhd m = nbhd (n ||| m)` — the intersection of two cofinite neighbourhoods
  removes the *union* `Eₙ ∪ Eₘ = E_{n ||| m}` of the excluded finite sets. This is Scott's
  `Eₙ ∪ Eₘ = E_k` with `k = n ||| m` (bitwise OR).
* `nbhd_injective`: `n ↦ nbhd n` is one-one (the converse-inclusion ordering Scott mentions; here we
  only need injectivity, from `Nat.eq_of_testBit_eq`).
* `PN` is the neighbourhood system `{nbhd n ∣ n}` over the token type `ℕ`; it is closed under
  intersection because `nbhd n ∩ nbhd m = nbhd (n ||| m)` is again a neighbourhood (so in fact *any*
  two neighbourhoods are consistent — `PN_consistent`).
* `PNpres` is the computable presentation: the enumeration is `nbhd`, the intersection function is
  the **choice-free primitive-recursive bitwise OR** `Domain.Recursive.myLor` (`= (· ||| ·)`,
  `myLor_eq_lor`), and Scott's relation 7.1(i) `nbhd n ∩ nbhd m = nbhd k ↔ (n ||| m) = k` is decided
  by `RecDecidable.natEq` (equality of two primitive-recursive functions). Relation 7.1(ii) is
  *always true* (any two neighbourhoods are consistent), so it is trivially recursively decidable.
* `PN_isEffectivelyGiven`: `PN` admits a computable presentation.

Everything is choice-free (`⊆ {propext, Quot.sound}`): all the bit-level facts go through mathlib's
`Nat.testBit_lor` / `Nat.eq_of_testBit_eq` (both `[propext, Quot.sound]`) and the bespoke
primitive-recursive `myLor`.
-/

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem







end DomainTheory.NeighbourhoodSystems.Example78
