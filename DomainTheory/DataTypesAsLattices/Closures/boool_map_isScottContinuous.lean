/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices



































theorem boool_map_isScottContinuous :
    IsScottContinuous (fun u => condSet u (ofNat 0) (succSet topElem)) :=
  condSet_isScottContinuous_left (ofNat 0) (succSet topElem)

end DomainTheory.DataTypesAsLattices
