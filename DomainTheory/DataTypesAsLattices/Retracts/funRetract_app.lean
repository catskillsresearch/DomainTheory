/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices









theorem funRetract_app (u : Pomega) :
    funOf funRetract u = graph (fun x => funOf u x) :=
  beta (graph_const_isScottContinuous (fun u x => funOf u x)
    (fun x => funOf_isScottContinuous_left x)) u

end DomainTheory.DataTypesAsLattices
