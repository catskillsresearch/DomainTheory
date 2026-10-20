/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.UComputablePresentation
import DomainTheory.Neighborhood.Exercise812g1a.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive NeighborhoodSystem

/-- `hD₀mne` for `U`: the master neighbourhood `U.master = Set.Ico 0 1` is non-empty. -/
theorem U_master_nonempty : U.master.Nonempty := ⟨0, by norm_num [U]⟩

end DomainTheory.Neighborhood
