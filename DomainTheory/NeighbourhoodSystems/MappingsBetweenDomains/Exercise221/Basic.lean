/-ai
This file gathers and re-exports the construction of the neighbourhood system C of Exercise 2.21: membership, the system itself, the total finite sequences and the total empty sequence, juxtaposition, the nested-or-disjoint comparisons of cones and singletons, and the lemmas on prepending a string to a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singletonElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Lambda
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.juxtapose
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_not_subset_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_ne_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_singleton_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singleton_cone_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.singleton_singleton_nd
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.nestedOrDisjoint_C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.subset_singleton_eq
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_prepend
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_subset_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_mono

@[expose] public section

/-!
# Exercise 2.21 (Scott 1981, PRG-19) — the system `𝒞`, total finite sequences, juxtaposition

The system `𝔹` of 2.3 has as its total elements only the *infinite* sequences: a finite prefix `σ`
only ever yields the **partial** element `σ⊥ = ↑(σΣ*)`, which can always be sharpened by a longer
prefix. We modify `𝔹` to a system `𝒞` having **both** finite and infinite sequences as total
elements (Scott's hint `𝔹 ⊆ 𝒞`).

The idea: keep the cones `σΣ* = cone σ` of `𝔹` (these give the partial `σ⊥` and, in the limit, the
infinite total sequences), and add for every finite `σ` a *terminator token* — the **singleton**
`{σ}`. The neighbourhood `{σ}` asserts "the sequence is exactly `σ` (terminated)". Because `{σ}` is
a minimal nonempty neighbourhood, `↑{σ}` is a *total* (maximal) element — this is the total finite
sequence `σ`. We thus distinguish:

* `Λ = ↑{[]}`  — the **total empty sequence** (terminated), and
* `⊥ = ↑Δ = ↑(cone [])` — the **undefined sequence**, with `⊥ ⊏ Λ`.

`𝒞 = {σΣ*} ∪ {{σ}}` is again pairwise nested-or-disjoint (a singleton sits inside a cone exactly
when its string extends the cone's prefix; two distinct singletons are disjoint), so it is a
neighbourhood system via `ofNestedOrDisjoint`, and visibly `𝔹 ⊆ 𝒞`.

**Juxtaposition `xy`.** We build `juxtapose : ApproximableMap₂ 𝒞 𝒞 𝒞` realizing the
left-to-right-biased concatenation:

* if `x` extends the prefix `σ` but is *not known to terminate* (a cone neighbourhood `σΣ* ∈ x`),
  the result only commits to the prefix `σ` — `xy ⊒ σ⊥`, independent of `y`. Hence **for an infinite
  (total) `x`, `xy = x` for all `y`** (`juxtapose_cone`);
* if `x` is the total finite sequence `σ` (the terminator `{σ} ∈ x`), the result is `σ` followed by
  `y`: `xy` prepends `σ` to `y` (`juxtapose_singleton_mem`).

This is the "strong left-to-right bias" Scott describes: `y` is consulted only after `x` is known to
have terminated.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-! ### The neighbourhood system `𝒞`: cones together with terminator singletons. -/


/-! ### Total elements: finite sequences `↑{σ}`, and `⊥ ⊏ Λ`. -/


/-! ### Prepending a string to a `𝒞`-neighbourhood. -/


/-! ### Juxtaposition `xy` as an approximable map of two variables. -/

end DomainTheory.NeighbourhoodSystems.Exercise221
