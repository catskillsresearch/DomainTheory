/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **A computable canonical bisection of a `ComputablePresentation`'s own neighbourhoods**: two
`Nat.Primrec` index functions `left`/`right` such that `Q.X (left k)`/`Q.X (right k)` are always
disjoint and reunite to `Q.X k`. (Nonemptiness of both pieces is *not* required here — for the
concrete `U`/`V` instances this file eventually builds (`(e)(b)`/`SplitU.lean`), it is automatic
from `mem → Set.Nonempty`, so is proved separately rather than carried as a field.)

**`left_congr`/`right_congr`** are a well-definedness requirement discovered while scoping `(e)(c)`
(2026-07-05), *not* present in the earlier `arxiv.md` draft of this structure: `ComputablePresentation.X`
is generally many-to-one (distinct raw indices `k`, `k'` can present the *same* set `Q.X k = Q.X k'`),
so building a genuine classical `split : Set α → Set γ → Set α → Set γ × Set γ` *function of sets*
out of an index-level `left`/`right` needs `left`/`right`'s *output sets* — not necessarily the raw
output indices themselves — to only depend on `Q.X k` as a set, or `(e)(c)`'s `posIdx_spec`/
`negIdx_spec` obligations (stated `∀ n m k`, not just for one fixed representative) would not be
provable. Satisfied by any canonicalizing construction (e.g. `SplitU.lean`'s `splitULeft`/
`splitURight`, built via `canonCode`, which already collapses every representative of a given set to
one canonical index) — expected free for both `(e)(b)`'s `SplitV.lean` and `(f)(a)`'s reuse of
`SplitU.lean`, but must be checked (or reduced to an existing `canonCode`/`canonIdx`-invariance lemma)
when those are actually built, not merely assumed. -/
structure ComputableBisection {γ : Type*} {W : NeighborhoodSystem γ} (Q : ComputablePresentation W) where
  /-- Index of the "left" half of `Q.X k`. -/
  left : ℕ → ℕ
  /-- Index of the "right" half of `Q.X k`. -/
  right : ℕ → ℕ
  /-- `left` is primitive recursive. -/
  left_primrec : Nat.Primrec left
  /-- `right` is primitive recursive. -/
  right_primrec : Nat.Primrec right
  /-- The two halves are disjoint. -/
  disjoint : ∀ k, Q.X (left k) ∩ Q.X (right k) = ∅
  /-- The two halves reunite to the whole. -/
  union : ∀ k, Q.X (left k) ∪ Q.X (right k) = Q.X k
  /-- `left`'s *output set* depends only on `Q.X k` as a set, not on which raw index represents it. -/
  left_congr : ∀ k k', Q.X k = Q.X k' → Q.X (left k) = Q.X (left k')
  /-- `right`'s *output set* depends only on `Q.X k` as a set, not on which raw index represents it. -/
  right_congr : ∀ k k', Q.X k = Q.X k' → Q.X (right k) = Q.X (right k')

end DomainTheory.NeighbourhoodSystems
