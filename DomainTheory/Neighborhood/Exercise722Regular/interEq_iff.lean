/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722
import Mathlib.Logic.Encodable.Basic
import DomainTheory.Neighborhood.Exercise722Regular.Basic


namespace DomainTheory.Neighborhood

namespace Exercise722
















/-- **Definition 7.1(i), syntactically**, is *exactly language equivalence on `SExpr`*:
`Xₙ ∩ Xₘ = X_k ↔ denote (cap eₙ eₘ) = denote e_k`. -/
theorem interEq_iff (a b k : SExpr) :
    denote a ∩ denote b = denote k ↔ denote (.cap a b) = denote k := by
  rw [denote_cap]

end Exercise722
end DomainTheory.Neighborhood
