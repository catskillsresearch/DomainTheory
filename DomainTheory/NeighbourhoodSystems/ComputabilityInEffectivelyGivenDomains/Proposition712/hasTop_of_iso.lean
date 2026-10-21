/-ai
Having a greatest element is preserved by an order isomorphism of element lattices, from the target system back to the source.

If t is greatest in the target, its inverse image is greatest in the source: for any element x, the isomorphism reflects the inequality of the image of x below t, and that inequality holds because t is greatest.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive


namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}


/-- **`HasTop` transports across domain isomorphisms.** An order-iso `|D| ≃o |D'|` carries the
greatest element of `|D'|` to that of `|D|`. -/
theorem hasTop_of_iso {D : NeighborhoodSystem γ} {D' : NeighborhoodSystem δ}
    (e : D.Element ≃o D'.Element) (h : HasTop D') : HasTop D := by
  obtain ⟨t, ht⟩ := h
  refine ⟨e.symm t, fun x => ?_⟩
  rw [← e.le_iff_le, e.apply_symm_apply]
  exact ht (e x)

end Counterexample712C
end DomainTheory.NeighbourhoodSystems
