/-ai
This file gathers and re-exports the constructions of Exercise 7.13: the inclusion structure, consistency and meet, the hint neighbourhoods and the hint system and its presentation, the inclusion structure of a computable presentation, reconstruction of elements in both directions and their order isomorphism, and the membership, inclusion, intersection, and meet lemmas used to relate them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.CONS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.MEET
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconElem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconElemInv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_top
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_subset_inter_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toNbhd_inter_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.toSystem_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.meet_iff_interEq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_INCL
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.mem_ofPresentation_toNbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.ofPresentation_toNbhd_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.reconstruct

@[expose] public section

/-!
# Exercise 7.13 (Scott 1981, PRG-19, §7) — effectively given domains ↔ an `INCL` relation on `ℕ`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.13.** Show that an effectively given domain can always be identified with a relation
> `INCL(n, m)` on integers, where the two derived relations
>
> * `CONS(n, m)  :↔  ∃ k. INCL(k, n) ∧ INCL(k, m)`               (consistency), and
> * `MEET(n, m, k) :↔ ∀ j. (INCL(j, k) ↔ INCL(j, n) ∧ INCL(j, m))` (binary meet)
>
> are both recursively decidable, and where the axioms hold:
>
> * (i)   `∀ n. INCL(n, n)`                                   (reflexive)
> * (ii)  `∀ n m k. INCL(n, m) ∧ INCL(m, k) → INCL(n, k)`      (transitive)
> * (iii) `∃ m ∀ n. INCL(n, m)`                               (a greatest code — the master `Δ`)
> * (iv)  `∀ n m. CONS(n, m) → ∃ k. MEET(n, m, k)`            (consistent pairs have a meet)
>
> (Hint: consider the neighbourhood system `𝒟 = { {m ∣ INCL(m, n)} ∣ n }`. Is this essentially any
> effectively given system?)

## What this file proves

`INCL(n, m)` is the integer image of `Xₙ ⊆ Xₘ`. The exercise is an **equivalence**, formalized here
in both directions plus the two round-trips:

* **`InclStructure`** — the abstract data Scott asks for: a relation `INCL` with recursively decidable
  `INCL`/`CONS`/`MEET`, and axioms (i)–(iv). Following the project's `ComputablePresentation`
  convention (which carries `inter` as primitive-recursive *data* rather than recovering it by an
  unbounded μ-search), we carry the *witnesses* of (iii)/(iv) as a master index `topIdx` and a
  primitive-recursive meet function `meetIdx`; the literal existential axioms (iii)/(iv) are then
  recovered as theorems (`axiom_iii`/`axiom_iv`).
* **(⇐) `InclStructure.toSystem` / `toPresentation` / `toSystem_isEffectivelyGiven`** — Scott's hint
  system `Sₙ = {m ∣ INCL(m, n)}` is a neighbourhood system and is *effectively given*. The crux is
  `toNbhd_subset_iff : Sₙ ⊆ Sₖ ↔ INCL(n, k)` (← by transitivity (ii), → because `n ∈ Sₙ` by
  reflexivity (i)); relation 7.1(i) is `MEET` (`toNbhd_inter_eq_iff`), 7.1(ii) is `CONS`.
* **(⇒) `ofPresentation`** — every effectively given domain yields such an `InclStructure` with
  `INCL n m := Xₙ ⊆ Xₘ`. The only non-trivial decidability is `MEET`: on an effectively given system
  `MEET(n, m, k) ↔ Xₙ ∩ Xₘ = Xₖ` (`meet_iff_interEq`; ⇒ uses that a `MEET` witness makes `(n, m)`
  consistent, hence `Xₙ ∩ Xₘ ∈ 𝒟` by `inter_mem`, hence enumerated by `surj`), so `MEET` is decided
  by the presentation's `interEq`.
* **Round-trip A `ofPresentation_toPresentation_INCL`** — `INCL ↦ 𝒟 ↦ INCL` recovers `INCL` exactly.
* **Round-trip B `reconstruct_isomorphic`** — `toSystem (ofPresentation P) ≅ᴰ V`: the reconstructed
  system *is* (domain-)isomorphic to the original, answering Scott's "Is this essentially any
  effectively given system?" with **yes**. (Exercise 7.18's *effective* isomorphism would tighten
  "essentially" to the effective level.)

## Choice discipline

The `INCL`/`CONS`/`MEET` deciders and the presentation *data* are built on the choice-free
`Recursive.lean` layer and audit `⊆ {propext, Quot.sound}`. `Set`-equality/membership reasoning over
the arbitrary carrier `α` (the `MEET ↔ interEq` proof, the isomorphism's filter/`OrderIso` laws)
pulls `Classical.choice` at the `Prop` level only — the same pattern as Theorems 7.4/7.5/7.10.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive


namespace InclStructure

variable (I : InclStructure)



/-! ### (⇐) Scott's hint system `Sₙ = {m ∣ INCL(m, n)}` -/










end InclStructure

/-! ### (⇒) Every effectively given domain yields an `InclStructure` -/

variable {α : Type*} {V : NeighborhoodSystem α}






/-! ### Round-trip A: `INCL ↦ 𝒟 ↦ INCL` recovers `INCL` -/

/-! ### Round-trip B: `toSystem (ofPresentation P) ≅ᴰ V`

Scott's "Is this essentially any effectively given system?" — the reconstructed system is
domain-isomorphic to the original. The finite-element correspondence is `Xₙ ↔ Sₙ` (inclusion-
preserving, since `Sₙ ⊆ Sₘ ↔ Xₙ ⊆ Xₘ`); we extend it to all elements (filters) via the mutually
inverse `reconElem`/`reconElemInv`, in the style of Exercise 1.20's `powerIso`. -/




end DomainTheory.NeighbourhoodSystems.Exercise713
