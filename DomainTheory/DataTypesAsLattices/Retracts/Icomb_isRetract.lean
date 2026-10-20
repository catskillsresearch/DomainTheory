/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.Icomb_app


namespace DomainTheory.DataTypesAsLattices





















theorem Icomb_isRetract : IsRetract Icomb := by
  change Icomb = graph (fun x => funOf Icomb (funOf Icomb x))
  have : (fun x => funOf Icomb (funOf Icomb x)) = fun x => x := by
    funext x
    simp [Icomb_app]
  rw [this]
  rfl

end DomainTheory.DataTypesAsLattices
