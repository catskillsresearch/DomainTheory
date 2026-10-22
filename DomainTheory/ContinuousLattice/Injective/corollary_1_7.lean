/-ai
A T₀-space is injective if and only if every space in which it is embedded admits a continuous retraction onto it.

If the space is injective, its identity extends along any embedding, and the extension is a retraction. Conversely, the embedding into the product of one copy of the Sierpiński space for each open set admits a retraction by hypothesis, and a retract of that injective power is injective.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2eof_retract
public import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski_power
public import DomainTheory.ContinuousLattice.Injective.proposition_1_5

@[expose] public section


open Topology TopologicalSpace

universe u


/-- **Scott 1972, Corollary 1.7.** A space is injective iff it is a retract of every
super-space of which it is a subspace. -/
theorem corollary_1_7 (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (e : D → Y), IsEmbedding e →
        ∃ r : C(Y, D), ∀ d, r (e d) = d := by
  constructor
  · intro hD Y _ e he
    obtain ⟨r, hr⟩ := hD e he (ContinuousMap.id D)
    exact ⟨r, hr⟩
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2
    exact IsInjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power (Opens D))
      (productOfMemOpens D) r hr
