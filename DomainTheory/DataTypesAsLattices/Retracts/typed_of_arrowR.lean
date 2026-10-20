/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app


namespace DomainTheory.DataTypesAsLattices









































theorem typed_of_arrowR {a b u : Pomega} (hu : typed u (arrowR a b)) :
    u = comp b (comp u a) := by
  simpa [typed, arrowR_app] using hu

end DomainTheory.DataTypesAsLattices
