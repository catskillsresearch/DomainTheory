/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- Scott's guard for `cond`, phrased with explicit equalities on the truth component
`C = inl⁻¹ W`. With `X = inl⁻¹ inr⁻¹ W` and `Y = inr⁻¹ inr⁻¹ W`:

* `C = {0}` (`true`):  `X ⊆ Z`;
* `C = {1}` (`false`): `Y ⊆ Z`;
* `C = Δ` (`⊥`):       `Δ_D ⊆ Z`. -/
def condGuard (V : NeighborhoodSystem α) (W : Set (Example12.Token ⊕ (α ⊕ α))) (Z : Set α) : Prop :=
  (Sum.inl ⁻¹' W = Example12.zero ∧ Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.one ∧ Sum.inr ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z) ∨
  (Sum.inl ⁻¹' W = Example12.master ∧ V.master ⊆ Z)

end DomainTheory.NeighbourhoodSystems.Exercise326
