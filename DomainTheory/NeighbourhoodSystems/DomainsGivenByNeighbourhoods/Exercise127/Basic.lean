/-ai
This file gathers and re-exports boundedness of a set of elements, the family of upper bounds, the least upper bound, the two-term sequence, and the nonemptiness of the upper bounds of a bounded set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.Bounded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.upperBounds
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.sSup
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.pairSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.upperBounds_nonempty

@[expose] public section

/-!
# Exercise 1.27 (Scott 1981, PRG-19, §1) — bounded sets and least upper bounds

Scott introduces *bounded* sets of elements as the analogue, for `|𝒟|`, of *consistent*
sequences of neighbourhoods. A set `X ⊆ |𝒟|` is **bounded** iff it has an upper bound
`y ∈ |𝒟|` (`x ⊑ y` for all `x ∈ X`), and then

`⊔X = ⋂ {y ∣ x ⊑ y for all x ∈ X}`

is its **least upper bound**. This file formalizes:

* `Bounded X` and `sSup X hX := sInf (upper bounds of X)` — the upper-bound family is non-empty
  exactly because `X` is bounded, so we reuse `sInf` from Exercise 1.18; the lub laws
  `le_sSup` / `sSup_le` are then immediate from `le_sInf` / `sInf_le`;
* `consistent_pair_iff_bounded` — for `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is `Consistent` iff
  `{↑U, ↑W}` is bounded ("boundedness is for elements what consistency is for neighbourhoods");
* `bounded_iff_finite_bounded` — **with the aid of Exercise 1.18**, `X` is bounded iff every
  *finite* subset of `X` is bounded; the hard direction builds the bound as the `leastFilter`
  of `C = ⋃_{x∈X} x`, whose finite consistency comes from the finite bounds.

The constructions (`sSup`) are `[propext, Quot.sound]`. The hard direction of
`bounded_iff_finite_bounded` selects a finite witness set via `Classical.choice`; this is a
*proof*, so the construction stays choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-! ### Boundedness of `{↑U, ↑W}` ⟺ consistency of `⟨U, W⟩`. -/


/-! ### Boundedness is finitary (with the aid of Exercise 1.18). -/
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
