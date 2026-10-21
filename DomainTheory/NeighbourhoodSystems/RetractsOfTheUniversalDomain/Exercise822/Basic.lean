/-ai
This file gathers and re-exports the development of Exercise 8.22: the doubling encoding and the completed encoding, their cons, nil, append, length, prefix, injectivity, and separation lemmas, the image family and the neighbourhood system D' with its master, membership, nested-or-disjoint law, and subsystem relation into B, the cone-subset translations and the separation of a cone from a singleton, the maps between elements of C and of D' with their membership and inverse laws, the order isomorphism of C with D', and the nonemptiness of every C-neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.memD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cdEquiv
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.C_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_append
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_length
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_length
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_prefix_of_prefix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_prefix_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_prefix_encC_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.not_encC_prefix_enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_prefix_encC_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_ne_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_subsystem_B
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_enc_subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_encC_subset_cone_enc_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.not_cone_enc_subset_cone_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_encC_subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_mem_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_mem_cone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_mem_singleton
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.fromD'_toD'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.toD'_fromD'

@[expose] public section

/-!
# Exercise 8.22 (Scott 1981, PRG-19, §8) — `B ⊴ C`, `C ⊴ B`, and general domain equations

> **EXERCISE 8.22.** Which of the two relations hold: `B ⊴ C` or `C ⊴ B`? Or do they both hold? In
> general if we use domain equations `D = T(D) + S(D)` and `E = T(E)`, will `E ⊴ D` hold? What
> projections do you see in the examples in 6.2?

Scott's staple examples of Example 6.2 satisfy `B ≅ B + B` and `C ≅ 𝟙 + C + C`, both presented over
the *same* token type `Str = List Bool` as the least families

`B = {Σ*} ∪ {0X ∣ X ∈ B} ∪ {1X ∣ X ∈ B}`,   `C = {Σ*} ∪ {{σ} ∣ σ ∈ Σ*} ∪ {0X ∣ X ∈ C} ∪ {1X ∣ X ∈ C}`,

i.e. `memB X ↔ ∃ σ, X = cone σ` and `memC X ↔ (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})` (`ExampleB.lean`,
`Example44.lean`). **Both `B ⊴ C` and `C ⊴ B` hold** — so the answer to "or do they both hold?" is
*yes*.

## `B ⊴ C` — the direct projection ("what projections do you see in the examples in 6.2")

Since `B` and `C` are literally systems over the *same* tokens with `B.mem ⊆ C.mem` (every
`B`-neighbourhood `cone σ` is already a `C`-neighbourhood), `B` is a **literal subsystem** of `C`
in the sense of Definition 6.10: `B ◁ C`. The only content is the `inter_closed` clause, which is
immediate from `cone_trichotomy` (two `B`-neighbourhoods are nested or disjoint; disjoint is
excluded because we're assuming the intersection is a nonempty `C`-neighbourhood). Proposition 6.12
then hands us the projection pair: `i : B → C` the identity inclusion, `j : C → B` the "collapse
extra completions back onto the enclosing cone" retraction — exactly the projection Scott is asking
us to notice in Example 6.2.

## `C ⊴ B` — a genuine combinatorial embedding

This is the more interesting direction, since `C` has "extra" elements — the completed finite
sequences `strElem σ = ↑{σ}` — that are not present at all in `B` (every `B`-element is either an
infinite sequence or a *properly extendable* partial one; `B` has no isolated/maximal element at a
finite position). Nonetheless `C` embeds into `B` via a concrete, choice-free re-encoding of tokens
that never needs to leave the finite-string world:

* **`enc : Str → Str`** doubles every bit (`enc [] = []`, `enc (b :: σ) = b :: b :: enc σ`), so
  `enc` is injective, monotone, and *prefix-reflecting* (`enc_prefix_iff : enc σ <+: enc τ ↔ σ <+: τ`)
  — it re-encodes `C`'s "still going" positions (`cone σ`) as `B`-cones `cone (enc σ)`.
* **`encC σ := enc σ ++ [true, false]`** appends the two-bit marker `[true, false]`, which can
  *never* be confused with a doubled block `[b, b]` (`b = b` always, `true ≠ false`) — this
  re-encodes `C`'s "completed" positions (`{σ}`) as a *further, deeper* `B`-cone `cone (encC σ)`
  that just happens to never get extended any further inside the image subsystem `D'`. The
  hard-won combinatorial facts (`enc_prefix_encC_iff`, `encC_prefix_encC_iff`,
  `not_encC_prefix_enc`) show this re-encoding exactly reproduces `C`'s own nesting/disjointness
  pattern of cones vs. singletons, all via ordinary structural induction on `Str` (no infinitary
  or choice machinery needed).
* **`D' : NeighborhoodSystem Str`** is the subfamily `{cone (enc σ)} ∪ {cone (encC σ)}` of `B`'s
  cones. Since *every* `D'`-neighbourhood is already a `B`-cone, `NestedOrDisjoint memD'` is free
  from `B`'s own `cone_trichotomy` (`D'_nestedOrDisjoint`), and `D' ◁ B` follows just as easily
  (`D'_subsystem_B`).
* **`toD'`/`fromD'`** transport `C`'s elements to `D'`'s elements and back (mirroring
  `Example62.toBB`/`fromBB`), giving the order-isomorphism `cdEquiv : C.Element ≃o D'.Element`
  hence `C ≅ᴰ D'`, and with `D' ◁ B` this is exactly `C ⊴ B` (`Lemma615.Trianglelefteq`).

## The general question: `D = T(D) + S(D)`, `E = T(E)` — will `E ⊴ D`?

Instantiating `T(X) := X + X`, `S(X) := 𝟙`: `B ≅ T(B)` and `C ≅ T(C) + S(C)`, so `B` plays the role
of `E` and `C` plays the role of `D` — and indeed `B ⊴ C` holds, as shown above. This matches the
general categorical picture (a direct generalization of Theorem 6.16's embedding argument): the sum
decomposition `D ≅ T(D) + S(D)` always gives a **projection pair** `T(D) ⊴ D` (project the `S(D)`
summand to the fresh bottom), not merely an *embedding* `T(D) ◁ D`; running Theorem 6.16's own
approximant-chain construction with this projection pair standing in for `D`'s Lambek isomorphism
(in place of the *full* isomorphism the original theorem uses) produces, from `E`'s own iso
`T(E) ≅ E` and `E`'s initiality, a genuine projection pair `E ⇄ D`, hence `E ⊴ D` — reusing exactly
the ladder/fixed-point machinery of `Theorem616.lean` with one side weakened from an isomorphism to
a retraction. We do not carry out this re-derivation in Lean here (it would essentially duplicate
`Theorem616.lean`'s ~250 lines with one hypothesis weakened); the concrete instance for `B`, `C`
above is a full, formally checked confirmation of the pattern the general argument predicts.

Everything proved here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-! ## Part 1 — `B ⊴ C` -/


/-! ## Part 2 — `C ⊴ B`

### The doubling encoding `enc` and the marked encoding `encC`. -/


















/-! ### The image subsystem `D'` and `D' ◁ B`. -/







/-! ### Subset facts for the image cones, translating `C`'s own cone/singleton facts. -/





/-! ### The forward map `toD' : C.Element → D'.Element`. -/


/-! ### The inverse map `fromD' : D'.Element → C.Element`. -/


/-! ### Membership characterizations, mirroring `Example62.toBB_mem_inj₀` etc. -/






/-! ### The two halves are mutually inverse. -/



/-! ### The domain isomorphism `C ≅ᴰ D'`, hence `C ⊴ B`. -/

end Exercise822
end DomainTheory.NeighbourhoodSystems
