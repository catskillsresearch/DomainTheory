/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.Exercise814.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}




section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)





























/-- **Exercise 8.14 (Scott 1981, PRG-19), the main theorem.** For any closure operator
`a : E → E`, the fixed-point set of `a` is a finitary domain. -/
theorem isFinitary_of_isClosureOperator (h : IsClosureOperator a) : IsFinitary a :=
  ⟨CompactFix h, domainOfClosure h, ⟨fixSetOrderIso h⟩⟩

end FiniteDomain
end DomainTheory.Neighborhood
