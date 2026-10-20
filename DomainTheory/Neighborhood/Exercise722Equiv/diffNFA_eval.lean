/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv.Basic
import DomainTheory.Neighborhood.Exercise722Equiv.diffNFA_evalFrom


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set










theorem diffNFA_eval (e1 e2 : SExpr) (w : List Bool) :
    (diffNFA e1 e2).eval w = {(evalFin e1 w, evalFin e2 w)} := by
  show (diffNFA e1 e2).evalFrom (diffNFA e1 e2).start w = _
  show (diffNFA e1 e2).evalFrom {(startFin e1, startFin e2)} w = _
  exact diffNFA_evalFrom e1 e2 w (startFin e1) (startFin e2)

end Exercise722
end DomainTheory.Neighborhood
