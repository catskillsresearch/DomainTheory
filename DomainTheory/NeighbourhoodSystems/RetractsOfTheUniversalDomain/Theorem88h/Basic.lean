module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88h.DiagFixed

@[expose] public section

/-!
# Theorem 8.8(c), Part 1 of 6 — the diagonal fixed-point predicate is recursively enumerable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Theorem 8.8(c):
the converse direction to Theorem 8.8(b) — a computable, finitary projection `a` of `𝒰` yields an
effectively given domain `{Y ∈ 𝒰 ∣ Y a Y} ◁ 𝒰` (Theorem 8.5's `fixedNbhd a`, already known to be a
subsystem for *any* approximable map `a`).

## This file

The naive plan ("`a`'s graph r.e. + `𝒰`-equality decidable ⟹ `{Y ∈ 𝒰 ∣ Y a Y}` r.e. ⟹ effectively
given") glosses over a real gap: `Xₙ a Xₙ` being merely **r.e.**, not decidable, means the raw index
set `S := {n ∣ Xₙ a Xₙ}` cannot be *filtered* directly into a `ComputablePresentation`'s enumeration
— `interEq_computable`/`cons_computable` need genuinely decidable relations and a *primitive
recursive* `.inter`. The 6-part plan (mirroring Theorem 8.8(b)'s style) starts here, with Part 1: pin
down `S`'s defining predicate (`DiagFixed`) and extract, from `a`'s computability, the underlying
recursively **decidable** witness relation that Parts 2–4 will gate a primitive-recursive fold on.

`DiagFixed P a n := a.rel (P.X n) (P.X n)` is exactly (`diagFixed_iff_fixedNbhd_mem`) the condition
`(fixedNbhd a).mem (P.X n)`, i.e. `P.X n` (already a `V`-neighbourhood) is a neighbourhood of Theorem
8.5's subsystem `fixedNbhd a = {X ∈ V ∣ X a X}`.

`diagFixed_isREPred` restricts `IsComputableMap P P a`'s two-variable r.e. relation `Xₙ a Xₘ` to the
diagonal `n = m` via `REPred.comp` against the primitive-recursive pairing `n ↦ ⟨n, n⟩` — no new
mathematical content, purely a reindexing of Definition 7.2's hypothesis.

`diagFixed_exists_qChar` then unfolds `REPred`'s own definition (`p n ↔ ∃ i, q ⟨i,n⟩` with `q`
recursively decidable via a `{0,1}`-valued primitive-recursive characteristic `qChar`) to expose that
characteristic function directly: `DiagFixed P a n ↔ ∃ i, qChar ⟨i,n⟩ = 1`. This `qChar` is exactly
what Theorem 8.8(c) Parts 2–4 (the gated fold `myFoldCode`, its invariant, and the `D`-side deciders)
will consume — no unbounded search is *primitive* recursive, but a fold that only ever *tests* an
already-produced index against `qChar` (rather than searching for a fresh witness) is.

All of this is stated for a general neighbourhood system `V` and computable presentation `P` (not
just `𝒰`), since none of the mathematics is specific to the universal domain; Theorem 8.8(c) itself
will specialize `V := 𝒰`, `P := UComputablePresentation`. Everything here is **choice-free**
(`⊆ {propext, Quot.sound}`): built only from `Definition72.lean`'s choice-free `IsComputableMap` and
`Recursive.lean`'s choice-free `REPred`/`RecDecidable` closure lemmas.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

end DomainTheory.NeighbourhoodSystems
