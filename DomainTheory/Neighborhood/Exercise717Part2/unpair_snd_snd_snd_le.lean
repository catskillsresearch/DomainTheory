/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise717
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Proposition77
import DomainTheory.Neighborhood.Exercise717Part2.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}
















theorem unpair_snd_snd_snd_le (c : ℕ) : c.unpair.2.unpair.2.unpair.2 ≤ c := by
  have h1 := unpair_snd_le c
  have h2 := unpair_snd_le c.unpair.2
  have h3 := unpair_snd_le c.unpair.2.unpair.2
  omega

end Exercise717
end DomainTheory.Neighborhood
