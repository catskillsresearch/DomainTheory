/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Scomb_mid_isScottContinuous
import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_app2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_app]
  exact beta (Scomb_mid_isScottContinuous f) g

end DomainTheory.DataTypesAsLattices
