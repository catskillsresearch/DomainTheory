/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- The two-variable elementwise bridge for a general `ApproximableMap₂`, specialized to a pair. -/
theorem toElementMap_ofMap₂_pair {β γ δ : Type*} {V₀ : NeighborhoodSystem β}
    {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ} (f₂ : ApproximableMap₂ V₀ V₁ V₂)
    (p : V₀.Element) (q : V₁.Element) :
    (ofMap₂ f₂).toElementMap (pair p q) = f₂.toElementMap₂ p q := by
  have h := toElementMap₂_toMap₂ (ofMap₂ f₂) p q
  rw [toMap₂_ofMap₂] at h
  exact h.symm

end DomainTheory.NeighbourhoodSystems
