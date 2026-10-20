/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Graph
import DomainTheory.DataTypesAsLattices.FixedPoint.Basic


namespace DomainTheory.DataTypesAsLattices



theorem iterateBot_mono {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∀ n, iterateBot f n ⊆ iterateBot f (n + 1)
  | 0 => by
    simp [iterateBot, botElem]
  | n + 1 =>
    isScottContinuous_monotone hf (iterateBot_mono hf n)

end DomainTheory.DataTypesAsLattices
