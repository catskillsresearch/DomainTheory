module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section


open Topology TopologicalSpace

universe v


/-- **Scott 1972, Proposition 1.4.** Retracts of injective spaces are injective. -/
theorem InjectiveSpace.of_retract {D : Type v} {D' : Type v}
    [TopologicalSpace D] [TopologicalSpace D'] (hD : InjectiveSpace.{u} D)
    (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    InjectiveSpace.{u} D' := by
  constructor
  intro X Y _ _ e he f
  obtain ⟨g, hg⟩ := hD.extension e he (s.comp f)
  refine ⟨r.comp g, fun x => ?_⟩
  show r (g (e x)) = f x
  rw [hg x]
  exact hrs (f x)
