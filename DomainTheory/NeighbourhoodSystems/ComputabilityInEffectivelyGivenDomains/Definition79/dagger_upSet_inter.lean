module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Definition 7.9 (remark 2).** "In that case `↓X ∩ ↓Y = ↓(X ∩ Y)`." When `{X, Y}` is
consistent (witness `Z ⊆ X ∩ Y`, `Z ∈ 𝒟`), the intersection `X ∩ Y` is again a neighbourhood,
so `↓X ∩ ↓Y = ↓(X ∩ Y)` is a neighbourhood of the prepared system `𝒟†`. (The unconditional set
identity `↓X ∩ ↓Y = ↓(X ∩ Y)` is Exercise 1.20's `upSet_inter`; the content here is membership
in `𝒟†`.) -/
theorem dagger_upSet_inter {X Y Z : Set α} (hX : V.mem X) (hY : V.mem Y) (hZ : V.mem Z)
    (hsub : Z ⊆ X ∩ Y) : V.dagger.mem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  exact ⟨X ∩ Y, V.inter_mem hX hY hZ hsub, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
