/-ai
This file gathers and re-exports the structure of an approximable map, directed unions of elements, the elementwise action, the identity map, composition, the map induced by a domain isomorphism, and extensionality of the relation, together with the membership lemma for the elementwise action, the relation lemmas for the identity and for composition, and the elementwise action of the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.sSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_idMap

@[expose] public section

/-!
# Lecture II (§2) — approximable mappings: Definitions 2.1, 2.2 and Theorems 2.5–2.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture II,
*Approximable mappings*. A mapping of domains that "preserves the spirit of approximation" is given
not by a function on ideal elements but by a **relation between neighbourhoods**: `X f Y` reads "if
the input is approximated at least as well as by `X`, then the output is approximated at least as
well as by `Y`."

This file formalizes the §2 core:

* **Definition 2.1** — `ApproximableMap V₀ V₁`: a relation `f ⊆ 𝒟₀ × 𝒟₁` with
  (i) `Δ₀ f Δ₁` (`master_rel`),
  (ii) `X f Y → X f Y' → X f (Y ∩ Y')` (`inter_right`, the consistency/intersectivity condition),
  (iii) `X f Y → X' ⊆ X → Y ⊆ Y' → X' f Y'` (`mono`, monotonicity: sharper input, blunter output).
  We carry `rel_dom`/`rel_cod` recording `f ⊆ 𝒟₀ × 𝒟₁`.
* **Proposition 2.2** — every approximable mapping determines an elementwise function
  `toElementMap f : |𝒟₀| → |𝒟₁|`, `f(x) = {Y ∣ ∃ X ∈ x, X f Y}`, which is a filter (i)–(iii) are
  *all* used); the relation is recovered by `rel_iff_mem_principal` (`X f Y ↔ Y ∈ f(↑X)`); the map
  is monotone (`toElementMap_mono`); and two approximable maps are equal iff they induce the same
  elementwise map (`ext_of_toElementMap`).
* **Theorem 2.5** — neighbourhood systems and approximable maps form a **category**: identity
  `idMap` (`X I_D Y ↔ X ⊆ Y`), composition `comp g f` (`X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`), with the
  identity laws `idMap_comp`/`comp_idMap` and associativity `comp_assoc`.
* **Proposition 2.6** — the elementwise action is a **functor** to sets and functions:
  `toElementMap_idMap` (`I_D(x) = x`) and `toElementMap_comp` (`(g∘f)(x) = g(f(x))`).
* **Theorem 2.7** — every domain **isomorphism** `e : |𝒟₀| ≃o |𝒟₁|` (Definition 1.9) comes from an
  approximable map: `ofIso e` with `toElementMap_ofIso` (`(ofIso e)(x) = e(x)`), packaged as
  `exists_approximable_of_iso`; moreover `e` carries finite (principal) elements to finite elements
  (`exists_principal_eq_apply_principal`), via the directed-union construction `sSupDirected`.

Everything in this file is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the only
classical lemma is `ext_of_toElementMap`, which decides neighbourhood membership by `by_cases`
(`Classical.em`). -/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem


end NeighborhoodSystem


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-! ### Theorem 2.5 — the category of neighbourhood systems and approximable mappings. -/


/-! ### Proposition 2.6 — the functor to sets and functions. -/


/-! ### Theorem 2.7 — every domain isomorphism comes from an approximable mapping. -/

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
