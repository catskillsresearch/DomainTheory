/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Graph
import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3_comp


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3 (The substitution theorem).** Continuous
functions of several variables on `Pω` are closed under substitution. -/
theorem theorem_1_3 {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) :=
  theorem_1_3_comp hf hg

end DomainTheory.DataTypesAsLattices
