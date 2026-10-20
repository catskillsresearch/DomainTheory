/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Z_isScottContinuous_left


namespace DomainTheory.DataTypesAsLattices
























theorem Zcomb_map_isScottContinuous (n : ℕ) :
    IsScottContinuous (fun f => graph (fun x => Z n f x)) :=
  graph_const_isScottContinuous (fun f x => Z n f x)
    (fun x => Z_isScottContinuous_left n x)

end DomainTheory.DataTypesAsLattices
