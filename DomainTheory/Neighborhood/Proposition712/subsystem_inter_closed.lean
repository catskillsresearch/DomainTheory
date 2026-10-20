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



/-- A subsystem of an unconditionally ∩-closed system is itself unconditionally ∩-closed: the
`◁`-clause `inter_closed` routes the intersection through `E`. -/
theorem subsystem_inter_closed {D E : NeighborhoodSystem γ} (h : D ◁ E)
    (hE : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y))
    {X Y : Set γ} (hX : D.mem X) (hY : D.mem Y) : D.mem (X ∩ Y) :=
  h.inter_closed hX hY (hE (h.sub hX) (h.sub hY))

end Counterexample712C
end DomainTheory.Neighborhood
