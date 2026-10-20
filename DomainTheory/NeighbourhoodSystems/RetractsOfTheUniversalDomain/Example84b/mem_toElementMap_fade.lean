/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- The closed form of `fade`'s elementwise action, generalized (via `mem_toElementMap₂_fade`) from
Example 8.4(a)'s ambient `D` to an arbitrary neighbourhood system `G`. -/
theorem mem_toElementMap_fade {γ : Type*} {G : NeighborhoodSystem γ} (t : O.Element) (w : G.Element)
    {Z : Set γ} :
    ((fade (D := G)).toElementMap (pair t w)).mem Z ↔
      G.mem Z ∧ (Z = G.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ w.mem Z)) := by
  rw [show (fade (D := G)) = ofMap₂ (fade₂ (D := G)) from rfl, toElementMap_ofMap₂_pair,
    mem_toElementMap₂_fade]

end DomainTheory.NeighbourhoodSystems
