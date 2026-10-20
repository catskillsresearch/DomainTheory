module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.restrictTo
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.sumMasterI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.isum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.ioplus
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iotimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprod_mem_slice_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi_mem_slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_restrictTo_cons
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_iprodNbhd_restrictTo
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.z_mem_of_slices
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi_toPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.proj_fromPi
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_not_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.index_of_some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_inter_same
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_mem_sumMasterI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI_subset_sumMasterI

@[expose] public section

/-!
# Exercise 6.29 (Scott 1981, PRG-19, §6) — infinitary sum and product

> **EXERCISE 6.29.** Generalize `+` and `×` to infinitary operations on domains:
> `∑_{n=0}^∞ D_n` and `∏_{n=0}^∞ D_n`. Would a similar generalization be possible for `⊕` and `⊗`?

We work with an arbitrary index type `ι` and a family of neighbourhood systems `D : ∀ i, 𝒟ᵢ` over
token types `α i` (Scott's `D_n`, with `ℕ` the intended `ι`). Tokens of the combined systems live in
`Σ i, α i` (for product-like operations) or `Option (Σ i, α i)` (for sum-like operations, the
`none` being the fresh basepoint). This is the indexed analogue of the abstract binary
`prod`/`sum` over `α ⊕ β` / `Option (α ⊕ β)`.

## The four operations and the answer

* **`∏_i D_i` (`iprod`)** — the indexed **product**. A neighbourhood is a tuple `X i ∈ 𝒟ᵢ` that is
  the master in all but **finitely many** coordinates (a *cylinder*). The finite-support condition
  is *essential*: it is exactly what makes the compact elements of the product the finitely-presented
  ones, giving the headline result `iprodEquiv : |∏_i D_i| ≃o ∀ i, |D_i|` (the product order is
  pointwise) — the infinitary **Proposition 3.2**.
* **`∑_i D_i` (`isum`)** — the indexed **separated sum**. A neighbourhood is the basepoint master or
  a single tagged copy `inj i X` of one summand (finite information — only one coordinate is
  constrained), so no finite-support condition is needed. Element trichotomy `isum_trichotomy`:
  every element is `⊥` or lives in exactly one summand.
* **`⊕_i D_i` (`ioplus`)** — the indexed **coalesced sum**, as `∑` but with the improper tagged
  copies deleted (the bottoms identified). Single-coordinate, so it **generalizes fine**.
* **`⊗_i D_i` (`iotimes`)** — the indexed **smash product**. A proper neighbourhood would need *every*
  coordinate proper (`≠` master), which over an infinite `ι` contradicts finite support. So the
  infinite smash **degenerates**: `iotimes_only_master`/`iotimes_subsingleton` — over an infinite
  index it has only the basepoint, a one-point domain.

**Answer to Scott's question.** `+`, `×`, `⊕` all generalize to infinitary operations; `⊗` does
**not** — the infinite smash collapses to the trivial domain.

**Choice discipline.** Every *data* construction is choice-free
(`iprod`, `isum`, `ioplus`, `iotimes`, the order iso `iprodEquiv`, and `isum_summand_unique` all have
`#print axioms ⊆ {propext, Quot.sound}`). The finite-support predicate is a `List` of coordinates in
its *positive* form `∀ i, i ∉ l → X i = master`, which keeps intersection (`FinSupp.inter`) and the
reconstruction (`z_mem_of_slices`) constructive. Only two genuinely classical Prop-level results
remain: `isum_trichotomy` (an excluded-middle case split on whether an element reaches a summand) and
the degeneracy `iotimes_only_master`/`iotimes_subsingleton` (a cardinality argument through Mathlib's
classical `Set.Finite`). Both are flagged in their docstrings.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-! ## The product neighbourhood and its algebra -/






variable {D : ∀ i, NeighborhoodSystem (α i)}




section IndexedProduct

variable [Nonempty ι]

/-! ## The element isomorphism `|∏_i D_i| ≃o ∀ i, |D_i|`

Throughout we use the *slices* `slice i U` — the cylinder that is `U` at coordinate `i` and the
master elsewhere. -/

section Iso

variable [DecidableEq ι]





















end Iso

end IndexedProduct

/-! ## `+` generalizes to `∑`: the indexed separated sum

Tokens live in `Option (Σ i, α i)`: the `none` basepoint plus tagged copies `inj i X` of the
summands. A neighbourhood constrains only a single coordinate, so — unlike the product — no
finite-support condition is needed. We need `∅ ∉ 𝒟ᵢ` (`hne`) to keep distinct tagged copies
disjoint. -/











/-! ## `⊕` generalizes: the indexed coalesced sum

As `∑`, but the *improper* tagged copies `inj i Δᵢ` are deleted (the per-summand bottoms are
identified with the basepoint). Single-coordinate, so it generalizes with no finite-support issue. -/


/-! ## `⊗` does **not** generalize: the infinite smash degenerates

The smash product keeps only those tuples that are *proper* (`≠` master) in **every** coordinate
(plus the basepoint master). Over an infinite index this collides with the finite-support
requirement that any neighbourhood imposes — there are no proper neighbourhoods at all, so the
infinite smash collapses to the one-point domain. -/

end Exercise629
end DomainTheory.NeighbourhoodSystems
