/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app


namespace DomainTheory.DataTypesAsLattices















theorem sumMed_isGraph (f g : Pomega) :
    sumMed f g = graph (fun u => funOf (sumMed f g) u) := by
  apply graph_ext
  intro u
  exact (sumMed_app f g u).symm

end DomainTheory.DataTypesAsLattices
