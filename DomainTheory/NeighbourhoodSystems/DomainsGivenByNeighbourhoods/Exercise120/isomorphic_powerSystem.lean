module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.20 (statement).** `𝒟` and its power system `𝒟'` are isomorphic. -/
theorem isomorphic_powerSystem : V ≅ᴰ V.powerSystem := ⟨V.powerIso⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
