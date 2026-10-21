/-ai
The approximable map carried by the constant function with value b, evaluated at any argument, returns b.

Unfold the constant-function map as the curry of the first projection, apply the curry law, and read the first component of the pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.embedFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.embedSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.constFunMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.evalBotMap

@[expose] public section

/-!
# Exercise 8.20 (Scott 1981, PRG-19)

> **Exercise 8.20.** For any system we know `D ⊴ D + D`, but what about
>
> `D ⊴ D × D` and `D ⊴ D → D`?
>
> Would these projections be computable if `D` is effectively given? Are there more than one
> projection pair in each case?

## What is formalized here

Both `D ⊴ D×D` and `D ⊴ (D→D)` hold **unconditionally, for every domain `D`** (no hypotheses
needed, unlike Exercise 8.19's `E×E ⊴ E`/`E+E ⊴ E`, which genuinely required `T ⊴ E` and
`E→E ⊴ E`). Both are exhibited by the *simplest possible* combinator recipe, generalized slightly
to two (possibly different) domains `A`, `B`:

* **Products** (`trianglelefteq_prod_fst`/`trianglelefteq_prod_snd`): embed `a ↦ ⟨a, ⊥⟩` (resp.
  `b ↦ ⟨⊥, b⟩`), retract with `proj₀` (resp. `proj₁`). `proj₀⟨a,⊥⟩ = a` on the nose, and
  `⟨(proj₀ z), ⊥⟩ = ⟨z.fst, ⊥⟩ ≤ ⟨z.fst, z.snd⟩ = z` since `⊥ ≤ z.snd` always
  (`Proposition 3.2(i)`'s `pair_le_pair_iff` reduces this to `⊥ ≤ z.snd`, `NeighborhoodSystem.bot_le`).
  Specializing `A = B = D` gives `D ⊴ D×D` (`D_trianglelefteq_prod`).
* **Function spaces** (`trianglelefteq_funSpace_const`): embed `b ↦ (λ_. b)` (the constant function,
  `constFunMap := curry (proj₀ B A)`), retract `φ ↦ φ(⊥)` (evaluate at the bottom,
  `evalBotMap := evalMap A B ∘ ⟨id, const ⊥⟩`). `eval(const_b) = b` on the nose
  (`toApproxMap_constFunMap`, from `toElementMap_curry_apply`), and `const_{φ(⊥)} ≤ φ` pointwise
  since `φ(⊥) ≤ φ(x)` for every `x` by **monotonicity of approximable maps**
  (`toElementMap_mono`, Proposition 2.2(iii)) applied to `⊥ ≤ x`. Specializing `A = B = D` gives
  `D ⊴ D→D` (`D_trianglelefteq_funSpace`).

**On `D ⊴ D+D`:** Scott states this as *already known* background (not part of the question), so
it is not re-derived here. The "easy half" of the projection pair is already in the codebase
(`outMap₀_comp_inMap₀`, Exercise 3.18); the second half (`inMap₀ ∘ outMap₀ ≤ id`, needing a
case-analysis on general sum elements analogous to the `which`/`condSum` machinery of Exercise 8.19)
is genuine additional work that this exercise does not ask for, so it is left as background
citation rather than re-proved.

**On multiplicity ("are there more than one projection pair"):** for products, the two
constructions above are already *literally different maps* whenever `D` has any element `≠ ⊥`
(`embedFst_ne_embedSnd_of_ne_bot`, by evaluating both at that element and reading off the first
coordinate) — so **yes**, generically more than one. For `D→D`, the "evaluate at a fixed point `a`"
half of the recipe is forced to be `a = ⊥` (for a *general* `a`, `const_{φ(a)} ≤ φ` would need
`φ(a) ≤ φ(x)` for *every* `x`, i.e. `a ≤ x` for every `x`, i.e. `a = ⊥`); but distinct projection
pairs can still arise by composing this one with any nontrivial order-automorphism of `D` (if
`D ≅ᴰ D` non-trivially, conjugating `constFunMap`/`evalBotMap` by the automorphism gives a genuinely
different pair). We do not formalize this second, automorphism-dependent source of multiplicity
here — it depends on `D`'s own automorphism group, which is not fixed data for a "for any system"
claim — but record it as the answer to Scott's question.

**On computability:** every combinator used (`⊥`, `paired`, `proj₀`/`proj₁`, `curry`, `evalMap`,
`constMap`) already has (or, for `constMap` at a fixed computable index such as `⊥`'s, trivially
would have) an `IsComputableMap` closure lemma elsewhere in the project (`proj₀_isComputable`/
`proj₁_isComputable`/`paired_isComputable`, `Theorem74.lean`; `curry_isComputable`/
`evalMap_isComputable`, `Theorem75.lean`) — so **yes**, both projection pairs are computable
whenever `D` is effectively given. Assembling the precise numerical parameters these lemmas expect
(the `ℕ → ℕ` encoding functions `gN`/`incl0`/`incl1`/`eq1` etc.) for *this specific* composite is
extra bookkeeping proportional to a full computable-presentation transport, not to this exercise's
mathematical content, so it is recorded here as a citation-backed answer rather than reformalized.

Everything proved here is **fully choice-free** (`⊆ {propext, Quot.sound}`): following the project's
"prefer `le_iff_toElementMap_le` + `le_antisymm` over `ext_of_toElementMap`" discipline
(`HANDOFF.md`), even the map *equalities* (`proj₀_comp_embedFst`, `proj₁_comp_embedSnd`,
`evalBotMap_comp_constFunMap`) are proved via `le_antisymm` on `le_iff_toElementMap_le`-unfolded
goals rather than `ApproximableMap.ext_of_toElementMap`, since both `≤`-directions are in fact
trivial (the underlying `toElementMap`s are literally equal, not just comparable) — so no
`Classical.choice` is pulled in anywhere, unlike most of `D`-mentioning Exercise 8.19.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v

/-! ## `A ⊴ prod A B` and `B ⊴ prod A B`, for any `A`, `B` -/

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


end Prod

/-! ## `B ⊴ funSpace A B`, for any `A`, `B` -/

section FunSpace

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


@[simp] theorem toApproxMap_constFunMap (b : B.Element) (a : A.Element) :
    (toApproxMap ((constFunMap A B).toElementMap b)).toElementMap a = b := by
  rw [constFunMap, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]

end FunSpace

/-! ## Exercise 8.20, specialized and assembled -/

variable {α : Type u} (D : NeighborhoodSystem α)
end DomainTheory.NeighbourhoodSystems
