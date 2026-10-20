module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_mono
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_single
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_cons
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_append
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kOut_mono

@[expose] public section

/-!
# Exercise 2.18 (Scott 1981, PRG-19, §2) — the "spacing" map `h : 𝔹 → 𝔹`

> **EXERCISE 2.18.** What is the meaning in words of the approximable mapping `h : 𝔹 → 𝔹`, where
> `h(0x) = 00 h(x)` and `h(1x) = 10 h(x)` for all `x ∈ |𝔹|`? Is `h` an isomorphism? Does there exist
> a map `k : 𝔹 → 𝔹` where `k ∘ h = I_𝔹`, and is `k` one-one?

**Meaning in words.** `h` *spaces the sequence out*: it copies each input symbol `b` and inserts a
`0` immediately after it. So the input bit `b` becomes the block `b0`, and `h` doubles the length of
every sequence, planting a `0` in every odd position (0-indexed positions `1, 3, 5, …`).

We follow the `Example24.runMap` template: a guaranteed-output function on finite prefixes drives the
neighbourhood relation `X h Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ 𝔹 ∧ (hOut σ)Σ* ⊆ Y`.

* `hOut σ` — the doubling of `σ` (each `b ↦ b0`); `hMap : ApproximableMap B B`.
* `kOut τ` — the left inverse on prefixes: keep the first bit of every *complete* pair, drop the
  inserted `0`; `kMap : ApproximableMap B B`. Key identity: `kOut (hOut σ) = σ`.
* `kMap_comp_hMap` — **`k ∘ h = I_𝔹`** (so the required `k` exists).
* `kMap_not_injective` — **`k` is *not* one-one**: `↑(0Σ*)` and `↑(1Σ*)` both map to `⊥` (the first
  bit of a length-1 prefix is an incomplete pair, hence dropped).
* `hMap_not_surjective` — **`h` is *not* an isomorphism**: it is not surjective (e.g. `↑(01Σ*)` is
  not in the range, since `h` only produces sequences with `0` in every odd position). `h` *is*
  injective (it has the left inverse `k`), so it is injective-but-not-surjective.

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`): everything is decidable list surgery. -/

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-! ### The doubling output `hOut` and its monotonicity. -/





/-! ### The inverse output `kOut` and its monotonicity. -/





/-! ### The approximable maps `hMap` and `kMap`. -/



/-! ### `k ∘ h = I`, `k` not injective, `h` not surjective. -/
end DomainTheory.NeighbourhoodSystems.Exercise218
