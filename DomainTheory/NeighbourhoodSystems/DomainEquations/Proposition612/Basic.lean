/-ai
This file gathers and re-exports Proposition 6.12: a subdomain determines a projection pair, an injection into the larger system and a projection back, with the projection composed after the injection equal to the identity on the subdomain and the injection composed after the projection contained in the identity on the larger system. The injection sends a neighbourhood to the neighbourhoods of the larger system that contain it, and the projection meets an element of the larger system with the subdomain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.ProjectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.projectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.proj_comp_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612.inj_comp_proj_le

@[expose] public section

/-!
# Lecture VI — Proposition 6.12 (Scott 1981, PRG-19): a subdomain yields a projection pair

**Proposition 6.12.** If `D ◁ E`, then there exists a *projection pair* of approximable mappings

`i : D → E` and `j : E → D`

with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`, determined as element-wise functions by

`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}` and `j(y) = y ∩ D`.

Scott leaves the proof "for the exercises". We give it directly at the level of the neighbourhood
relations (Definition 2.1), which keeps everything **choice-free**.

* The injection `i` (`Subsystem.inj`) is the relation `X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆ Y` — it sends a
  `D`-neighbourhood to all the `E`-neighbourhoods it refines.
* The projection `j` (`Subsystem.proj`) is the relation `Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y ⊆ X` — it
  intersects an `E`-element with `D`.

The two laws are then short relational calculations:

* `Subsystem.proj_comp_inj : j ∘ i = I_D`. Both round trips factor as `X ⊆ Y ⊆ Z`, giving exactly
  the identity relation `X ⊆ Z` on `D`. (Proved with the **choice-free** relational extensionality
  `ApproximableMap.ext`.)
* `Subsystem.inj_comp_proj_le : i ∘ j ⊆ I_E`. A round trip `Y ⊆ X ⊆ Y'` through a common
  `D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E` — but not conversely, so this direction is
  only an inclusion. The crucial clause of `D ◁ E` (consistency inherited from `E`) is what makes
  `j`'s output-intersection law hold (`inter_right`).

The element-wise descriptions Scott records are `Subsystem.toElementMap_inj` and
`Subsystem.toElementMap_proj`.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}








end Subsystem
end DomainTheory.NeighbourhoodSystems
