module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Proposition 7.12 — monotonicity of `{·}` on principal inputs.** When `X' ⊆ X`, the join
`{↑X'}` is blunter than `{↑X}` in `|ℙ𝒟|`. -/
theorem PDsingleton_mono {X X' : Set α} (hX : V.mem X) (hX' : V.mem X') (hX'X : X' ⊆ X) :
    V.PDsingleton (V.principal hX) ≤ V.PDsingleton (V.principal hX') := by
  intro W hW
  rw [PDmem_singleton] at hW ⊢
  obtain ⟨Y, hYpr, hPD, hsub⟩ := hW
  rw [mem_principal] at hYpr
  exact ⟨Y, ⟨hYpr.1, hX'X.trans hYpr.2⟩, hPD, hsub⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
