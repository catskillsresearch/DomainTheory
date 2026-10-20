/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
import DomainTheory.DataTypesAsLattices.Retracts.boolR_app
import DomainTheory.DataTypesAsLattices.Retracts.dcondSet_bool_idem


namespace DomainTheory.DataTypesAsLattices


































































theorem boolR_isRetract : IsRetract boolR := by
  apply graph_ext
  intro u
  rw [boolR_app, boolR_app, dcondSet_bool_idem]

end DomainTheory.DataTypesAsLattices
