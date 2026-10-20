/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set










theorem diffNFA_evalFrom (e1 e2 : SExpr) (w : List Bool)
    (S1 : Finset (autState e1)) (S2 : Finset (autState e2)) :
    (diffNFA e1 e2).evalFrom {(S1, S2)} w =
      {(w.foldl (stepFin e1) S1, w.foldl (stepFin e2) S2)} := by
  induction w generalizing S1 S2 with
  | nil => rfl
  | cons c w ih =>
    show (diffNFA e1 e2).evalFrom ((diffNFA e1 e2).stepSet {(S1, S2)} c) w = _
    rw [NFA.stepSet_singleton]
    show (diffNFA e1 e2).evalFrom {(stepFin e1 S1 c, stepFin e2 S2 c)} w = _
    exact ih (stepFin e1 S1 c) (stepFin e2 S2 c)

end Exercise722
end DomainTheory.Neighborhood
