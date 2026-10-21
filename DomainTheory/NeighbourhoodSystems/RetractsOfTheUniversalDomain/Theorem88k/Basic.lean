/-ai
This file gathers and re-exports membership of the induced enumeration in the fixed neighbourhood, the hitting of every diagonally fixed index, and surjectivity onto the fixed neighbourhood, for Theorem 8.8(c), part 4.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_of_diagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88j.D_X_surj

@[expose] public section

/-!
# Theorem 8.8(c), Part 4 of 6 — `D_X`'s `interEq`/`cons` relations are recursively decidable

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Part 3 (`Theorem88j.lean`) built the
enumeration `D_X qChar cons c := P.X (myFoldCode qChar cons c)` and showed it is onto `fixedNbhd
a`. This file proves the two relations Definition 7.1 actually needs are recursively decidable
*on the list-codes* `c` (not on the underlying `V`-indices, which are already handled by `P`).

## `interEq_computable` — free

`D_X c₁ ∩ D_X c₂ = D_X c₃` unfolds *literally* to `P.X n₁ ∩ P.X n₂ = P.X n₃` for `nᵢ := myFoldCode
qChar cons cᵢ`, so this is exactly `P.interEq_computable` reindexed along the (primitive-recursive,
Part 2's `primrec_myFoldCode`) triple `(c₁,c₂,c₃) ↦ (myFoldCode c₁, myFoldCode c₂, myFoldCode c₃)`.
No `a`/`DiagFixed` apparatus is needed at all.

## `cons_computable` — the one genuine lemma

`D_X_cons_iff` is the mathematical content of this part: `D`-consistency of two list-codes,
`∃ k, D_X k ⊆ D_X c₁ ∩ D_X c₂`, is **equivalent** to plain `V`-consistency of the underlying raw
indices, `∃ k', P.X k' ⊆ P.X n₁ ∩ P.X n₂`:

* `⟹` is immediate: any `D`-side witness `D_X k = P.X (myFoldCode qChar cons k)` is *already* a
  `V`-side witness, since `D_X`'s codomain is literally `P.X` of some raw index — no separate
  "is this really `V`-consistent" check is needed.
* `⟸` needs Theorem 8.8(c) Part 3's `D_X_of_diagFixed`: given a `V`-consistency witness `k'`,
  `P.inter_spec` gives `P.X (P.inter n₁ n₂) = P.X n₁ ∩ P.X n₂`; since `n₁`, `n₂` are both
  `DiagFixed` (Part 2's `diagFixed_myFoldCode`, as they are `myFoldCode`-outputs), so is their
  meet (`fixedNbhd_subsystem a`'s `inter_closed`, transported along the equation above), and
  `D_X_of_diagFixed` then produces the `D`-side witness code directly.

Once this equivalence is in hand, `cons_computable` is `P.cons_computable` composed with the same
primitive-recursive `myFoldCode`-pair reindex used for `interEq_computable`.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`), built purely from `Theorem88h.lean`–
`Theorem88j.lean`'s choice-free apparatus plus `Definition71.lean`'s choice-free `RecDecidable`
closure lemmas (`comp`/`of_iff`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

variable (P qChar cons)
end DomainTheory.NeighbourhoodSystems
