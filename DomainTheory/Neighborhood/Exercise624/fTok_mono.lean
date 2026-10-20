/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619PartB
import DomainTheory.Neighborhood.Exercise624.Basic
import DomainTheory.Neighborhood.Exercise624.gTok_mono


namespace DomainTheory.Neighborhood

open NeighborhoodSystem DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise624




/-- `fTok` is monotone in both arguments. -/
theorem fTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : fTok p q ⊆ fTok p' q' :=
  gTok_mono hp (gTok_mono hp hq)

end Exercise624
end DomainTheory.Neighborhood
