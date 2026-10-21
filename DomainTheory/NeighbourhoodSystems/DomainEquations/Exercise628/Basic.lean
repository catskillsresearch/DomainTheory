/-ai
This file gathers and re-exports Lemma 6.15, Proposition 6.12, the order embedding of elements induced by a projection pair, and the predicate that a neighbourhood system has finitely many neighbourhoods, as the shared preliminaries for Exercise 6.28.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.projElementEmbedding
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.IsFinite

@[expose] public section

/-!
# Exercise 6.28 (Scott 1981, PRG-19, §6) — Plotkin's finite Cantor–Schröder–Bernstein

> **EXERCISE 6.28.** (Suggested by G. Plotkin). Show that if `𝒟` and `ℰ` are *finite* systems and
> `𝒟 ⊴ ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. Need the same be true of infinite systems?

Here `⊴` is Scott's *embeds-as-a-subdomain* relation of Lemma 6.15: `D ⊴ E` means `D ≅ᴰ D'` for
some subdomain `D' ◁ E`.

## The argument

The whole proof rests on a single observation: **`D ⊴ E` already supplies an order embedding of
element domains `|D| ↪o |E|`** (`Trianglelefteq.elementEmbedding`). Indeed, unfolding `⊴` gives an
order isomorphism `e : |D| ≃o |D'|` onto a subdomain `D' ◁ E`, and Proposition 6.12 turns `D' ◁ E`
into a projection pair `i : D' → E`, `j : E → D'` with `j ∘ i = I`. The element-wise map `i(·)` is
then an order embedding (`projElementEmbedding`): it is monotone (`toElementMap_mono`), and `j(·)`
is a monotone left inverse, so `i(a) ⊑ i(b) → j(i(a)) ⊑ j(i(b)) → a ⊑ b`. Compose with `e`.

For **finite** domains, mutual order embeddings force an isomorphism
(`orderIso_of_embeddings`): each embedding is injective, so the two finite element types have equal
cardinality, whence either embedding is a bijection — a surjective strictly-monotone map, i.e. an
order isomorphism. This is the finite Cantor–Schröder–Bernstein, and it is exactly what Plotkin's
hint exploits. (The retraction structure of `⊴` is *stronger* than a mere embedding, but the proof
only needs the embedding.)

"Finite system" is read faithfully as *finitely many neighbourhoods*
(`NeighborhoodSystem.IsFinite`); this yields `Finite |D|` (`finite_element_of_isFinite`) because a
filter is pinned down by which of the finitely many neighbourhoods it contains.

**Need the same be true of infinite systems?** **No.** Plotkin's hint is the finite cardinality
count above; it has no infinite analogue. Mutual *retracts* of dcpos need not be isomorphic — the
analogue of Cantor–Schröder–Bernstein fails for the retraction preorder once the domains are
infinite (a Eilenberg-swindle-style obstruction). Only the finite statement is formalized here; the
infinite counterexample is recorded as prose, outside this file's scope.

Everything is **choice-free at the relational core** (`projElementEmbedding`,
`elementEmbedding` audit to `{propext, Quot.sound}`); the finite count
(`orderIso_of_embeddings`, hence the main theorems) uses `Classical.choice` — genuinely
unavoidable, as it extracts a `Fintype` from `Finite` and a surjection's section.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## An order embedding `|D| ↪o |E|` from a projection pair / from `⊴` -/


/-! ## Finite Cantor–Schröder–Bernstein for ordered types -/

/-! ## Exercise 6.28 — the finite statement -/

/-! ## "Finite system" = finitely many neighbourhoods -/

end DomainTheory.NeighbourhoodSystems
