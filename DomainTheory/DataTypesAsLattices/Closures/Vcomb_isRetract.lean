/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app
import DomainTheory.DataTypesAsLattices.Closures.eq_5_19


namespace DomainTheory.DataTypesAsLattices
































theorem Vcomb_isRetract : IsRetract Vcomb := by
  change Vcomb = graph (fun a => funOf Vcomb (funOf Vcomb a))
  apply graph_ext
  intro a
  exact (Vcomb_app a).symm.trans (eq_5_19 a).symm

end DomainTheory.DataTypesAsLattices
