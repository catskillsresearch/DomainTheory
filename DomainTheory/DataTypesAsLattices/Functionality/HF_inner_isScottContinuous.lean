/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Hstep_isScottContinuous_e


namespace DomainTheory.DataTypesAsLattices















































theorem HF_inner_isScottContinuous (H : Pomega) :
    IsScottContinuous (fun e => graph (fun t => Hstep H e t)) :=
  graph_const_isScottContinuous (fun e t => Hstep H e t)
    (fun t => Hstep_isScottContinuous_e H t)

end DomainTheory.DataTypesAsLattices
