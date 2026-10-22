/-ai
One cone is contained in another if and only if the second prefix is an initial segment of the first.

From the inclusion, the first prefix lies in its own cone and therefore in the second cone. Conversely, an initial-segment relation composes with membership in the smaller cone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Str
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_cone

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Cones reverse the prefix order.** `σΣ* ⊆ τΣ*` iff `τ` is an initial segment of `σ`: a longer
prefix carves out a *smaller* cone. (`→` tests at `σ ∈ σΣ*`; `←` is transitivity of `<+:`.) -/
theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

end DomainTheory.NeighbourhoodSystems.ExampleB
