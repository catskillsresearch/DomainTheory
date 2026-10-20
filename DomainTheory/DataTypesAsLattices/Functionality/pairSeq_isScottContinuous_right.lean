/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices















theorem pairSeq_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun y z => condSet z x (condSet (predSet z) y botElem))
    (fun z =>
      theorem_1_3 (condSet_isScottContinuous_right z x)
        (condSet_isScottContinuous_mid (predSet z) botElem))

end DomainTheory.DataTypesAsLattices
