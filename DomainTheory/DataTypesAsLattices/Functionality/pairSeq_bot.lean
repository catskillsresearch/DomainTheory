/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices















theorem pairSeq_bot : pairSeq botElem botElem = botElem := by
  have hbody : (fun z => condSet z botElem (condSet (predSet z) botElem botElem)) =
      fun _ => botElem := by
    funext z
    ext n
    simp [condSet, botElem]
  simpa [pairSeq, seq2, hbody] using graph_const_bot

end DomainTheory.DataTypesAsLattices
