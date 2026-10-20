/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Theorem614.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}














































/-- For a strict map `g`, `g(⊥) = ⊥` relationally: `g` sends `Δ` only to `Δ`. -/
theorem strict_rel_master {β₀ β₁ : Type w} {V₀ : NeighborhoodSystem β₀}
    {V₁ : NeighborhoodSystem β₁} {g : ApproximableMap V₀ V₁} (hg : IsStrict g) {Z : Set β₁} :
    g.rel V₀.master Z ↔ Z = V₁.master :=
  ⟨fun h => hg h, fun h => h ▸ g.master_rel⟩

end Theorem614
end DomainTheory.Neighborhood
