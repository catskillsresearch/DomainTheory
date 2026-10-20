/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Scomb_map_isScottContinuous


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_app (f : Pomega) :
    funOf Scomb f =
      graph (fun v => graph (fun x => funOf (funOf f x) (funOf v x))) :=
  beta Scomb_map_isScottContinuous f

end DomainTheory.DataTypesAsLattices
