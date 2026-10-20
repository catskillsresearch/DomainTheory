/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
import all Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
import all Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.IsRetractSubspace

@[expose] public section

/-!
# Injective spaces (Scott 1972, §1)

Scott's §1 introduces *injective* `T₀`-spaces — those with the extension property for
continuous maps along subspace embeddings — and shows the two-point Sierpiński space is
injective, that injectivity is preserved by products and by retracts, and (the embedding
theorem) that every `T₀`-space embeds in a power of the Sierpiński space.

## Main definitions / results

* `IsInjectiveSpace` — Scott's Definition 1.1.
* `proposition_1_2` … `proposition_1_5` — Scott's Propositions 1.2–1.5.
* `corollary_1_6`, `corollary_1_7` — Scott's Corollaries 1.6 and 1.7.
-/

/-- Scott's two-point Sierpiński space 𝕆: `Prop` with the Sierpiński topology. -/
abbrev Sierpinski := Prop

open Topology TopologicalSpace

universe u v w

/-- **Scott 1972, Definition 1.1.** A topological space `D` is *injective* when, for every
topological embedding `e : X → Y` and every continuous `f : X → D`, there is a continuous
`g : Y → D` extending `f` along `e`. -/
def IsInjectiveSpace (D : Type v) [TopologicalSpace D] : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y),
    IsEmbedding e → ∀ f : C(X, D), ∃ g : C(Y, D), ∀ x, g (e x) = f x
