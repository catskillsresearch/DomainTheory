/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.SplitU
import DomainTheory.Neighborhood.Exercise812e
import DomainTheory.Neighborhood.UBisection2.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem














theorem zero_le_listMaxSnd (L : List (ℚ × ℚ)) : 0 ≤ listMaxSnd L := foldl_maxSnd_seed_le L 0

end DomainTheory.Neighborhood
