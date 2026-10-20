module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_interEq_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88k.D_X_cons_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88l.D_inter

@[expose] public section

/-!
# Theorem 8.8(c), Part 5 of 6 — a primitive-recursive `.inter` for `D_X`, and its `inter_spec`

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Parts 1–4 built the enumeration `D_X qChar
cons c := P.X (myFoldCode qChar cons c)`, showed it is onto `fixedNbhd a`, and showed its
`interEq`/`cons` relations are recursively decidable. This file supplies the last data field
`ComputablePresentation` needs: a primitive-recursive `D_inter : ℕ → ℕ → ℕ` with `D_X (D_inter c₁
c₂) = D_X c₁ ∩ D_X c₂` whenever the two are `D`-consistent.

## The construction: `D_inter c₁ c₂ := appendListCode c₁ c₂`

Concatenating the two list-codes (`Recursive.lean`'s Exercise 7.22 `appendListCode`/
`primrec_appendListCode`/`appendListCode_eq`, reused outright) is exactly right because
`myFoldCode` is a *left* fold from `P.masterIdx`, so folding the concatenated list decomposes
(`List.foldl_append`) as folding `c₂`'s list *starting from* `myFoldCode c₁` instead of from
`P.masterIdx`:

```
myFoldCode (appendListCode c₁ c₂) = (decodeList c₂).foldl myStep (myFoldCode c₁)
```

## The one genuine lemma: refolding from a smaller start intersects

`myFoldl_inter_of_le` is the mathematical content: for a list `l`, refolding it from a
`DiagFixed`-irrelevant starting point `n ⊆ r` (in `P.X`) reproduces `P.X n ∩ P.X (fold from r)`,
**provided** the two are already known `V`-consistent at the *end* of the fold. The key subtlety
is that `myStep`'s gate (`cons (Nat.pair r e.unpair.2) = 1`) is *accumulator-dependent*, so
refolding the same list from a smaller start could in principle skip steps the original fold took.
The induction shows this never happens: any step that *succeeds* from `r` also succeeds from `n`,
because the global witness (consistency of `n` with the *final* fold value) is inherited by every
intermediate accumulator via the fold's monotone-shrinking property (`myFoldl_subset`); and any
step that *fails* from `r` also fails from `n`, since success from the (⊆-smaller) `n` would imply
success from `r` too (monotonicity of `cons`'s witness in the ⊆ direction).

Given this, Part 5's `D_X_inter_spec` is immediate: unfold both sides via `appendListCode_eq`/
`List.foldl_append`, apply `myFoldl_inter_of_le` with `n := myFoldCode c₁`, `r := P.masterIdx`
(using `V.sub_master` for `n ⊆ r`), and the hypothesis (already `V`-side, since `D_X`'s codomain
*is* `P.X` of some raw index — no reindexing needed, unlike Part 4's `cons_iff`).

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`): `Recursive.lean`'s
`list_eq_of_getD`/`appendListTabFn_eq`/`primrec_appendListTabFn`/`primrec_appendListCode` were
tightened in this session (dropping a stray `by_contra`/lemma-set `simp` that pulled in
`Classical.choice`) to be choice-free outright, so no new taint is introduced here.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

/-! ### The one genuine lemma: refolding from a smaller, globally-consistent start -/

/-! ### `D_inter`, its primitive-recursiveness, and `inter_spec` -/


variable (P qChar cons)

variable {P qChar cons}
end DomainTheory.NeighbourhoodSystems
