/-ai
A retract of an injective space is injective.

Given an embedding and a continuous map into the retract, compose the map with the section into the injective space, extend the composite along the embedding, and compose the extension with the retraction. The retraction-section identity recovers the original map on the image of the embedding.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic

@[expose] public section


open Topology TopologicalSpace

universe v


/-- **Scott 1972, Proposition 1.4.** Retracts of injective spaces are injective. -/
theorem IsInjectiveSpace.of_retract {D : Type v} {D' : Type v}
    [TopologicalSpace D] [TopologicalSpace D'] (hD : IsInjectiveSpace.{u} D)
    (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' := by
  intro X Y _ _ e he f
  obtain ⟨g, hg⟩ := hD e he (s.comp f)
  refine ⟨r.comp g, fun x => ?_⟩
  show r (g (e x)) = f x
  rw [hg x]
  exact hrs (f x)
