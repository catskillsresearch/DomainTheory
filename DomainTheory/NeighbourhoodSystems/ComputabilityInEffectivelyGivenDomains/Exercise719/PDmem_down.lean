/-ai
A neighbourhood of the power domain is downward closed. If it contains a neighbourhood Z and X is a neighbourhood contained in Z, then it contains X.

A power-domain neighbourhood is a union of principal up-sets. The member Z lies under some generator of that union, and the smaller neighbourhood X still lies under the same generator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)

/-- **`ℙ𝒟`-neighbourhoods are downward closed.** If `Z ∈ A` and `X ⊆ Z` with `X ∈ 𝒟`, then `X ∈ A`
(each `A = ⋃ ↓Xᵢ` is a union of down-sets). -/
theorem PDmem_down {A : Set (Set α)} (hA : V.PDmem A) {Z X : Set α}
    (hZ : Z ∈ A) (hXZ : X ⊆ Z) (hX : V.mem X) : X ∈ A := by
  obtain ⟨L, hL, rfl⟩ := hA
  obtain ⟨X', hX', _, hZsub⟩ := (V.mem_PDunion).mp hZ
  exact (V.mem_PDunion).mpr ⟨X', hX', hX, hXZ.trans hZsub⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
