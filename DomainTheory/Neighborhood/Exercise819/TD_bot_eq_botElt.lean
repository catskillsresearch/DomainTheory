/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Exercise326Sum
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise819.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section General

variable {α β γ δ : Type*}

/-- **`TD.bot = Example23.botElt`.** These are the *same* element (`TD` and `Example23.T` are both
`Example12.neighborhoodSystem`), but not syntactically unifiable by `rfl` (the `abbrev`s don't
delta-reduce transparently through `NeighborhoodSystem.bot`'s field projection), so we prove it by
antisymmetry instead. -/
theorem TD_bot_eq_botElt : TD.bot = Example23.botElt :=
  le_antisymm (NeighborhoodSystem.bot_le _ _) (Example23.botElt_le _)

end General
end DomainTheory.Neighborhood
