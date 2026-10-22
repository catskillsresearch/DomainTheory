/-ai
The preparation of a neighbourhood system is the power system whose tokens are the neighbourhoods of the original system and whose neighbourhoods are their down-sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.PDmem

@[expose] public section

/-!
# Definition 7.9 (Scott 1981, PRG-19, §7) — the Smyth power domain `ℙ𝒟`

Scott closes Lecture VII with "an example of another kind of domain construct", the
*Smyth Power Domain*. For any neighbourhood system `𝒟` it builds a new system `ℙ𝒟` whose
elements behave like *sets of elements* of `𝒟`.

**Definition 7.9.** For a neighbourhood system `𝒟`,

`ℙ𝒟 = { ⋃_{i<n} (↓Xᵢ) ∣ ∀ i<n. Xᵢ ∈ 𝒟 }`,

where the **down-set** of `X ∈ 𝒟` is `↓X = {Y ∈ 𝒟 ∣ Y ⊆ X}`. The finite unions can be
*empty* (`n = 0`), giving the neighbourhood `∅`.

Two surrounding remarks Scott records as part of the definition:

* The construct is made *isomorphism-invariant* by first **preparing** `𝒟`: replace it by the
  isomorphic positive system `𝒟† = {↓X ∣ X ∈ 𝒟}` (Exercise 1.20). Then `ℙ𝒟` is the closure of
  `𝒟†` under finite unions.
* `↓X ∩ ↓Y ≠ ∅` iff `{X, Y}` is consistent in `𝒟`, and in that case `↓X ∩ ↓Y = ↓(X ∩ Y)`.

## What this file formalizes

Scott's `↓X` of §7 is *exactly* the set `Exercise 1.20` already named `upSet`
(`{Y ∈ 𝒟 ∣ Y ⊆ X}`), and the preparation `𝒟†` is exactly Exercise 1.20's `powerSystem`
(here aliased `dagger`, with the iso `dagger_isomorphic : 𝒟 ≅ᴰ 𝒟†` reusing
`isomorphic_powerSystem`). On top of those we add:

* `PDmem` — the neighbourhood family of `ℙ𝒟` (finite unions of down-sets, indexed by a
  `List` of `𝒟`-neighbourhoods; the empty list realizes the empty union `n = 0`);
* `mem_PDunion` / `PDmem_empty` / `PDmem_upSet` / `PDmem_master` / `PDmem_union` — the basic
  membership facts that pin the family down (it contains `∅`, every down-set `↓X`, the
  master `↓Δ`, and is closed under binary — hence finite — union);
* `PDmem_iff_fin` — the same family written with Scott's `⋃_{i<n}` (a `Fin n → Set 𝒟`);
* the two displayed remarks: `upSet_inter_nonempty_iff` (`↓X ∩ ↓Y ≠ ∅ ↔ {X,Y}` consistent)
  and, in the consistent case, `dagger_upSet_inter` (`↓X ∩ ↓Y = ↓(X∩Y) ∈ 𝒟†`); the
  unconditional set identity `↓X ∩ ↓Y = ↓(X∩Y)` is Exercise 1.20's `upSet_inter`.

This is everything Scott states as part of Definition 7.9 itself; that `ℙ𝒟` is *itself a
neighbourhood system*, effectively given when `𝒟` is, is the separate **Proposition 7.10**
(`Proposition710.lean`). Everything here is choice-free (`⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.9 — the preparation `𝒟†`.** Scott prepares `𝒟` for the power-domain
construct by replacing it with the isomorphic system `𝒟† = {↓X ∣ X ∈ 𝒟}`, which is exactly
Exercise 1.20's `powerSystem` (over the token type `Δ† = 𝒟`, i.e. `Set α`). It is a *positive*
neighbourhood system (`powerSystem_isPositive`). -/
abbrev dagger : NeighborhoodSystem (Set α) := V.powerSystem


/-! ### Definition 7.9 — the two displayed intersection remarks -/
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
