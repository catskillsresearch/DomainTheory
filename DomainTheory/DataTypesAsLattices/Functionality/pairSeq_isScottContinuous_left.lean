/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices















theorem pairSeq_isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun x z => condSet z x (condSet (predSet z) y botElem))
    (fun z => condSet_isScottContinuous_mid z _)

end DomainTheory.DataTypesAsLattices
