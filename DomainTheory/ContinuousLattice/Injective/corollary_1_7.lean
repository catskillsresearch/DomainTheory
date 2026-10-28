module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.Separation.Basic
import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power
import DomainTheory.ContinuousLattice.Injective.proposition_1_5

@[expose] public section


open Topology TopologicalSpace

universe u


/-- **Scott 1972, Corollary 1.7.** A space is injective iff it is a retract of every
super-space of which it is a subspace. -/
theorem corollary_1_7 (D : Type u) [TopologicalSpace D] [T0Space D] :
    InjectiveSpace.{u,u} D ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (e : D → Y), IsEmbedding e →
        ∃ r : C(Y, D), ∀ d, r (e d) = d := by
  constructor
  · intro hD Y _ e he
    obtain ⟨r, hr⟩ := hD.extension e he (ContinuousMap.id D)
    exact ⟨r, hr⟩
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2
    exact InjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power (Opens D))
      (productOfMemOpens D) r hr
