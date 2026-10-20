/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition711
public import DomainTheory.Neighborhood.Definition72
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Product
public import DomainTheory.Neighborhood.Proposition710
public import DomainTheory.Neighborhood.Theorem74
public import DomainTheory.Neighborhood.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Proposition712.Basic
public import DomainTheory.Neighborhood.Proposition712.hasTop_of_inter_closed
public import DomainTheory.Neighborhood.Proposition712.subsystem_inter_closed
public import DomainTheory.Neighborhood.Proposition712.hasTop_of_iso

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}



/-- **`D ⊴ ℙ𝒟` forces `|D|` to have a greatest element.** This is the obstruction behind Part C. -/
theorem hasTop_of_trianglelefteq_powerDomain {D : NeighborhoodSystem γ} {E : NeighborhoodSystem δ}
    (h : D ⊴ E.PowerDomain) : HasTop D := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  have hPcl : ∀ {X Y : Set (Set δ)}, E.PowerDomain.mem X → E.PowerDomain.mem Y →
      E.PowerDomain.mem (X ∩ Y) := fun hX hY => E.PDmem_inter hX hY
  exact hasTop_of_iso e (hasTop_of_inter_closed D' (subsystem_inter_closed hsub hPcl))

end Counterexample712C
end DomainTheory.Neighborhood
