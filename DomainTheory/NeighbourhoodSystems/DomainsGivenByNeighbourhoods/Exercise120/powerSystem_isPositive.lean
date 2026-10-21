/-ai
The power system is positive: the intersection of two of its neighbourhoods is again a neighbourhood if and only if the intersection is nonempty.

The intersection of the up-sets of two neighbourhoods is the up-set of their intersection. If that up-set equals the up-set of some neighbourhood, the neighbourhood itself lies in it. Conversely, a neighbourhood contained in the intersection is a consistency witness, so the intersection is a neighbourhood and its up-set is a neighbourhood of the power system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.20 — `𝒟'` is positive.** `↑X ∩ ↑Y = ↑(X∩Y)` is a neighbourhood iff it is
non-empty: a witness `Z ⊆ X ∩ Y` gives `X ∩ Y ∈ 𝒟`; conversely `↑W` always contains `W`. -/
theorem powerSystem_isPositive : V.powerSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.upSet_inter]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨W, hW, subset_rfl⟩
  · rintro ⟨Z, hZmem, hZsub⟩
    exact ⟨X ∩ Y, V.inter_mem hX hY hZmem hZsub, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
