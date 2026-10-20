module


public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **A split function is computable relative to two presentations** `P` (`α`-side), `Q` (`γ`-side)
when its two outputs are indexed by primitive-recursive functions of the three input indices
(indices of `A` in `P`, `B` in `Q`, `Xn` in `P`). Only the two index functions are data; primitive-
recursiveness and correctness (`posIdx_spec`/`negIdx_spec`) are `Prop`s, so this is choice-free. -/
structure IsComputableSplit {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
    (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (split : Set α → Set γ → Set α → Set γ × Set γ) where
  /-- Index (in `Q`) of `(split (P.X n) (Q.X m) (P.X k)).1`, as a function of the three input
  indices `n, m, k`. -/
  posIdx : ℕ → ℕ → ℕ → ℕ
  /-- Index (in `Q`) of `(split (P.X n) (Q.X m) (P.X k)).2`. -/
  negIdx : ℕ → ℕ → ℕ → ℕ
  /-- `posIdx` is primitive recursive (on the `Nat.pair n (Nat.pair m k)` coding, matching
  `RecDecidable₃`'s convention). -/
  posIdx_primrec : Nat.Primrec (fun t => posIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
  /-- `negIdx` is primitive recursive. -/
  negIdx_primrec : Nat.Primrec (fun t => negIdx t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
  /-- `posIdx n m k` genuinely indexes the split's first output **whenever that output is
  non-empty**. This is conditional (not `∀ n m k, … = Q.X (posIdx n m k)` outright) for a load-
  bearing reason found 2026-07-06 while repairing 8.12(g): `Q.X j` is *never* literally `∅` (every
  `ComputablePresentation` index is `Q.mem`-genuine, `Q.mem_X`), yet `SplitSpec'` (`Exercise812c.lean`)
  — the abstract correctness contract `atomPairG`'s classical layer needs `splitX`/`splitY` to
  satisfy — *requires* `(split A B Xn).1 = ∅` exactly when `A ∩ Xn = ∅`. An *unconditional*
  `posIdx_spec` is therefore jointly unsatisfiable with `SplitSpec'` for *any* split function
  whatsoever (not just a specific concrete one) — see `arxiv.md`'s 8.12(g) rows for the full
  argument. Weakening to "conditional on non-emptiness" is the fix: it costs nothing at any call
  site that already knows (from context, typically via `SplitSpec'`'s own emptiness ↔ clause) that
  the relevant output is non-empty — which is every existing use in this file — while making the
  structure satisfiable by a genuine `Set`-valued split whose output is sometimes literally `∅`. -/
  posIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).1 ≠ ∅ →
    (split (P.X n) (Q.X m) (P.X k)).1 = Q.X (posIdx n m k)
  /-- `negIdx n m k` genuinely indexes the split's second output whenever that output is
  non-empty. See `posIdx_spec`'s docstring for why this is conditional. -/
  negIdx_spec : ∀ n m k, (split (P.X n) (Q.X m) (P.X k)).2 ≠ ∅ →
    (split (P.X n) (Q.X m) (P.X k)).2 = Q.X (negIdx n m k)

end DomainTheory.NeighbourhoodSystems
