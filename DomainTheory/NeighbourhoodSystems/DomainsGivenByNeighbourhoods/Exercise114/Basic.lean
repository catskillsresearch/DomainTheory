module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.fin
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.nonempty_of_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.ns_mem

@[expose] public section

/-!
# Exercise 1.14 (Scott 1981, PRG-19, §1) — finite non-empty subsets of `ℕ`

Let `Δ = ℕ` and take as neighbourhoods the **finite non-empty** subsets of `ℕ`, together with `Δ`
itself. This is the infinite analogue of Example 1.5 (where `Δ` was finite).

Deliverables:

* `neighborhoodSystem : NeighborhoodSystem ℕ` — "Show that this is a neighbourhood system." Unlike
  the tail/binary examples this is *not* nested-or-disjoint (two finite sets may overlap partially),
  so condition (ii) is checked by hand: the consistency witness `Z ⊆ X ∩ Y` keeps `X ∩ Y` non-empty,
  and `X ∩ Y` is finite as soon as either factor is.
* **Finite elements.** `fin h = ↑X` (the principal filters), Scott's finite elements.
* **Total elements.** "What are the total elements?" The maximal filters are exactly the principals
  of *singletons*: `singleton_isTotal` shows `↑{n}` is total (a filter strictly above it would have
  to contain a set missing `n`, forcing `∅ ∈ 𝒟`).

Constructive (`[propext, Quot.sound]`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem





/-! ### Finite elements (principals) and total elements (singletons). -/


end DomainTheory.NeighbourhoodSystems.Exercise114
