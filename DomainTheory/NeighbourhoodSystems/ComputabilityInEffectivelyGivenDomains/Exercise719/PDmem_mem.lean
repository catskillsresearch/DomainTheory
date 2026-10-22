module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)

/-- **Every member of a `ℙ𝒟`-neighbourhood is a `𝒟`-neighbourhood.** -/
theorem PDmem_mem {A : Set (Set α)} (hA : V.PDmem A) {X : Set α} (hX : X ∈ A) : V.mem X := by
  obtain ⟨L, hL, rfl⟩ := hA
  obtain ⟨X', _, hXmem, _⟩ := (V.mem_PDunion).mp hX
  exact hXmem

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
