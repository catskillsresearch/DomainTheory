/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise823
import DomainTheory.Neighborhood.Exercise824.Basic
import DomainTheory.Neighborhood.Exercise824.pairSpace_bot_snd
import DomainTheory.Neighborhood.Exercise824.iterElem_zero_pair


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}











theorem bOp_zero (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    bOp s t 0 = constMap E E.bot := by
  show toApproxMap ((paired s t).iterElem 0).snd = constMap E E.bot
  rw [iterElem_zero_pair, pairSpace_bot_snd, Exercise823.toApproxMap_bot_eq_constMap]

end Exercise824
end DomainTheory.Neighborhood
