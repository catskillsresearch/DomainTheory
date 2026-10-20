/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

/-- **Exercise 7.13 — the abstract data.** A relation `INCL : ℕ → ℕ → Prop` together with the
witnesses and decidability/axiom data Scott requires. The derived relations are
`CONS`/`MEET` (below); the literal existential axioms (iii)/(iv) are `axiom_iii`/`axiom_iv`.

We carry `topIdx` (a master code) and a primitive-recursive `meetIdx` as *data* — exactly mirroring
`ComputablePresentation`, which carries its `inter` function as primitive-recursive data rather than
recovering it by an unbounded search. This is the faithful "effective" reading of axioms (iii)/(iv).
-/
structure InclStructure where
  /-- Scott's integer inclusion relation `INCL(n, m)` (the image of `Xₙ ⊆ Xₘ`). -/
  INCL : ℕ → ℕ → Prop
  /-- A primitive-recursive meet function: an index of the binary meet of consistent codes. -/
  meetIdx : ℕ → ℕ → ℕ
  /-- A master code (witness of axiom (iii)). -/
  topIdx : ℕ
  /-- `INCL` is recursively decidable. -/
  incl_dec : RecDecidable₂ INCL
  /-- `CONS(n, m) ↔ ∃ k. INCL(k, n) ∧ INCL(k, m)` is recursively decidable. -/
  cons_dec : RecDecidable₂ (fun n m => ∃ k, INCL k n ∧ INCL k m)
  /-- `MEET(n, m, k) ↔ ∀ j. (INCL(j, k) ↔ INCL(j, n) ∧ INCL(j, m))` is recursively decidable. -/
  meet_dec : RecDecidable₃ (fun n m k => ∀ j, INCL j k ↔ (INCL j n ∧ INCL j m))
  /-- The meet function is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  meetIdx_primrec : Nat.Primrec (fun t => meetIdx t.unpair.1 t.unpair.2)
  /-- **(i)** `INCL` is reflexive. -/
  incl_refl : ∀ n, INCL n n
  /-- **(ii)** `INCL` is transitive. -/
  incl_trans : ∀ {n m k}, INCL n m → INCL m k → INCL n k
  /-- **(iii)** the master code `topIdx` is `INCL`-greatest. -/
  topIdx_spec : ∀ n, INCL n topIdx
  /-- **(iv)** `meetIdx n m` is a `MEET` of `n, m` whenever `(n, m)` is consistent. -/
  meetIdx_spec : ∀ {n m}, (∃ k, INCL k n ∧ INCL k m) →
    ∀ j, INCL j (meetIdx n m) ↔ (INCL j n ∧ INCL j m)

end DomainTheory.NeighbourhoodSystems.Exercise713
