/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise213
public import DomainTheory.Neighborhood.Exercise215.Basic

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise215

open DomainTheory.Neighborhood NeighborhoodSystem














/-- `⊥ ⊑ ⊤`. -/
theorem botElt_le_topElt : botElt ≤ topElt := O.bot_le _

end DomainTheory.Neighborhood.Exercise215
