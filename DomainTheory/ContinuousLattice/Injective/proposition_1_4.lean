module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Topology TopologicalSpace

universe u v

theorem proposition_1_4 {D : Type v} {D' : Type v} [TopologicalSpace D] [TopologicalSpace D']
    (hD : InjectiveSpace.{u} D) (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    InjectiveSpace.{u} D' := by
  constructor
  intro X Y _ _ e he f
  obtain ⟨g, hg⟩ := hD.extension e he (s.comp f)
  refine ⟨r.comp g, fun x => ?_⟩
  show r (g (e x)) = f x
  rw [hg x]
  exact hrs (f x)
