module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem


/-- Each member of a directed family approximates the directed union. -/
theorem le_sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {a : V.Element} (ha : a ∈ S) :
    a ≤ V.sSupDirected S hne hdir :=
  fun _ hZ => ⟨a, ha, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
