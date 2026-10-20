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

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}



/-- An unconditionally ∩-closed system has a greatest element. -/
theorem hasTop_of_inter_closed (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : HasTop E :=
  ⟨improperTop E hcl, fun x _X hX => x.sub hX⟩

end Counterexample712C
end DomainTheory.Neighborhood
