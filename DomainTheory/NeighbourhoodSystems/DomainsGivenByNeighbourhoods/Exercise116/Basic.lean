/-ai
This file gathers and re-exports the cofinite neighbourhood system, the filter of an excluded-point set, the excluded-point set of a filter, the order isomorphism with the power set of the natural numbers, the neighbourhood system of all subsets, the membership simplifications, membership of singleton complements and of complements of finite sets, inclusion in a singleton complement, and the two theorems inverting the excluded-point correspondence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteIso
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.fullSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_toExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_compl_singleton
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_compl_of_finite
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.subset_compl_singleton
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded_toExcluded

@[expose] public section

/-!
# Exercise 1.16 (Scott 1981, PRG-19, §1) — cofinite subsets of `ℕ`

`Δ = ℕ`, `𝒟 =` the *cofinite* subsets (`Xᶜ` finite). This is a neighbourhood system
(`cofiniteSystem`), closed under all finite intersections. Scott asks to show
`|𝒟| ≅ (𝒫(ℕ), ⊆)`.

The order-isomorphism `cofiniteIso : |𝒟| ≃o Set ℕ` sends a filter `x` to its set of
**excluded points** `toExcluded x = {n ∣ {n}ᶜ ∈ x}`, with inverse
`ofExcluded E = {Y cofinite ∣ Yᶜ ⊆ E}` (a filter for *every* `E ⊆ ℕ`). The key reconstruction
lemma is `mem_compl_of_finite`: `⋂_{n∈F} {n}ᶜ = Fᶜ ∈ x` for finite `F` of points whose
single-point deletions are in `x`.

We also record `ofExcluded_univ_isTotal` / `le_ofExcluded_univ` — the unique total element is the
`⊑`-top `ofExcluded ℕ` (= all of `𝒟`), matching the greatest element `ℕ ∈ 𝒫(ℕ)` — and
`fullSystem`, a second system (all subsets) closed under finite intersection.

`mem_compl_of_finite` uses `Set.Finite.induction_on` (and `Set.Finite` is classical), so the
classification lemmas are not choice-free; the *constructions* (`ofExcluded`, `cofiniteSystem`)
are `[propext, Quot.sound]`.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem













/-! ### Total elements. -/

/-! ### A second `∩`-closed system: all subsets. -/

end Cofinite
end DomainTheory.NeighbourhoodSystems
