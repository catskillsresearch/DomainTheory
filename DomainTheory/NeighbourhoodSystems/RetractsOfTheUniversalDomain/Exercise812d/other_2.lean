module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **`IsComputableDiff P`**: set-difference relative to the presentation `P` is computable — a
primitive-recursive `diffIdx : ℕ → ℕ → ℕ` indexing `X n \ X m` whenever that difference is a
genuine neighbourhood (`diffIdx_spec`, mirroring `inter_spec` exactly), together with a decider
for that very side-condition (`diff_computable`, mirroring `cons_computable`). Only `diffIdx` is
data; the rest are `Prop`s, so this stays choice-free to *state* (any particular instance may of
course need `Classical.choice` to *construct*, exactly like `inter`/`cons_computable` themselves
would for an arbitrary effectively-given system). -/
structure IsComputableDiff {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V) where
  /-- Index of `X n \ X m`, as a function of the two input indices. -/
  diffIdx : ℕ → ℕ → ℕ
  /-- `diffIdx` is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  diffIdx_primrec : Nat.Primrec (fun t => diffIdx t.unpair.1 t.unpair.2)
  /-- `diffIdx n m` genuinely indexes `X n \ X m` whenever that difference is (exactly) some
  `X k` — i.e. whenever it is a genuine neighbourhood. -/
  diffIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n \ P.X m) → P.X (diffIdx n m) = P.X n \ P.X m
  /-- **7.1(i)-for-`\`**: "`X n \ X m` is a genuine neighbourhood" is recursively decidable in
  `n, m`, mirroring `cons_computable`'s role for `∩`. -/
  diff_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n \ P.X m)

end DomainTheory.NeighbourhoodSystems

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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **`IsComputableUnion P`**: set-union relative to the presentation `P` is computable — a
primitive-recursive `unionIdx : ℕ → ℕ → ℕ` indexing `X n ∪ X m` whenever that union is a genuine
neighbourhood (`unionIdx_spec`, mirroring `inter_spec`/`IsComputableDiff.diffIdx_spec` exactly),
together with a decider for that side-condition (`union_computable`, mirroring
`cons_computable`/`IsComputableDiff.diff_computable`). Only `unionIdx` is data; the rest are
`Prop`s, so this stays choice-free to *state* (any particular instance may of course need
`Classical.choice` to *construct*, exactly like `inter`/`cons_computable`/`IsComputableDiff`
themselves would for an arbitrary effectively-given system). -/
structure IsComputableUnion {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    where
  /-- Index of `X n ∪ X m`, as a function of the two input indices. -/
  unionIdx : ℕ → ℕ → ℕ
  /-- `unionIdx` is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  unionIdx_primrec : Nat.Primrec (fun t => unionIdx t.unpair.1 t.unpair.2)
  /-- `unionIdx n m` genuinely indexes `X n ∪ X m` whenever that union is (exactly) some `X k` —
  i.e. whenever it is a genuine neighbourhood. -/
  unionIdx_spec : ∀ {n m : ℕ}, (∃ k, P.X k = P.X n ∪ P.X m) → P.X (unionIdx n m) = P.X n ∪ P.X m
  /-- **7.1(i)-for-`∪`**: "`X n ∪ X m` is a genuine neighbourhood" is recursively decidable in
  `n, m`, mirroring `cons_computable`'s role for `∩`. -/
  union_computable : RecDecidable₂ (fun n m => ∃ k, P.X k = P.X n ∪ P.X m)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- Pack a two-sided code state: `idx0` (`P₀`-index of `A_n`), `idx1` (`P₁`-index of `B_n`),
`junk` (`1` iff `A_n = B_n = ∅` already). -/
def packState2 (idx0 idx1 junk : ℕ) : ℕ := Nat.pair idx0 (Nat.pair idx1 junk)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def stateIdx0 (s : ℕ) : ℕ := s.unpair.1

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

@[simp] theorem stateIdx0_packState2 (a b c : ℕ) : stateIdx0 (packState2 a b c) = a := by
  unfold stateIdx0 packState2; simp only [unpair_pair_fst]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def stateIdx1 (s : ℕ) : ℕ := s.unpair.2.unpair.1

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

@[simp] theorem stateIdx1_packState2 (a b c : ℕ) : stateIdx1 (packState2 a b c) = b := by
  unfold stateIdx1 packState2; simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def stateJunk (s : ℕ) : ℕ := s.unpair.2.unpair.2

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

@[simp] theorem stateJunk_packState2 (a b c : ℕ) : stateJunk (packState2 a b c) = c := by
  unfold stateJunk packState2; simp only [unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- Pack the persistent bit-source remainder `rem` alongside the current two-sided
`packState2`-shaped inner state `s`. -/
def packStateC (rem s : ℕ) : ℕ := Nat.pair rem s

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

def xwB1 (w : ℕ) : ℕ := w.unpair.2.unpair.1

end XSubStep

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

def xwN (w : ℕ) : ℕ := w.unpair.1

end XSubStep

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

def xwS (w : ℕ) : ℕ := w.unpair.2.unpair.2

end XSubStep

end DomainTheory.NeighbourhoodSystems
