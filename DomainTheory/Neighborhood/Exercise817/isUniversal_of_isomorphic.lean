/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88a
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise817.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}











/-- **Universality transports along isomorphism.** If `W` is universal and `W ≅ᴰ W'`, then `W'` is
universal too: every countable `D` embeds in `W` (`D ⊴ W`), and `W ⊴ W'` (take `D' := W'` in `⊴`'s
definition, using `Subsystem.refl` and the given isomorphism), so `trianglelefteq_trans` finishes. -/
theorem isUniversal_of_isomorphic {W : NeighborhoodSystem β} {W' : NeighborhoodSystem γ}
    (hW : IsUniversal.{u} W) (hWW' : W ≅ᴰ W') : IsUniversal.{u} W' := by
  have hWW'_tri : W ⊴ W' := hWW'.elim fun e => ⟨W', Subsystem.refl W', ⟨e⟩⟩
  intro α D _
  exact trianglelefteq_trans (hW D) hWW'_tri

end DomainTheory.Neighborhood
