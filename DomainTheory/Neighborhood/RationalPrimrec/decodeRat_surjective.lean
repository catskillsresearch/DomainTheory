/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RationalPrimrec.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive









/-- `decodeRat` is surjective: every rational number is `decodeRat` of some code (namely
`encodeRat q`). -/
theorem decodeRat_surjective : Function.Surjective decodeRat :=
  fun q => ⟨encodeRat q, decodeRat_encodeRat q⟩

end DomainTheory.Neighborhood
