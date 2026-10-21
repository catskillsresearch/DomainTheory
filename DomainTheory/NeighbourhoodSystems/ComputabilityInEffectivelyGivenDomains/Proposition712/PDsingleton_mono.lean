/-ai
If a neighbourhood X' is contained in a neighbourhood X, then the singleton of the principal element of X lies below the singleton of the principal element of X'.

A power-domain neighbourhood of the left singleton is witnessed by a neighbourhood Y of the principal element of X, together with a power-domain neighbourhood and a down-set inclusion. Principal membership gives the inclusion of X in Y, which composes with the inclusion of X' in X to give the inclusion of X' in Y, so the same data witness membership on the right.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

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
