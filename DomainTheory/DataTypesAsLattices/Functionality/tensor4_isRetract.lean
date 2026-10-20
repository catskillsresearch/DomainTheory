/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.tensor4_app
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_one
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_two
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app_three


namespace DomainTheory.DataTypesAsLattices
































theorem tensor4_isRetract {a b c d : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c) (hd : IsRetract d) :
    IsRetract (tensor4 a b c d) := by
  change tensor4 a b c d =
    graph (fun u => funOf (tensor4 a b c d) (funOf (tensor4 a b c d) u))
  apply graph_ext
  intro u
  rw [tensor4_app, tensor4_app, seq4_app_zero, seq4_app_one, seq4_app_two,
    seq4_app_three, retract_app ha, retract_app hb, retract_app hc, retract_app hd]

end DomainTheory.DataTypesAsLattices
