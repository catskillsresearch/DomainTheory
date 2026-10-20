/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise812
import DomainTheory.Neighborhood.IntervalPrimrec
import DomainTheory.Neighborhood.Theorem88
import DomainTheory.Neighborhood.Exercise812c.Basic
import DomainTheory.Neighborhood.Exercise812c.U_diff_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem







theorem U_diffClosed : U.DiffClosed := fun hX hY => U_diff_mem hX hY

end DomainTheory.Neighborhood
