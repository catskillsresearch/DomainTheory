/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boool_app
import DomainTheory.DataTypesAsLattices.Closures.boool_idem


namespace DomainTheory.DataTypesAsLattices



































theorem boool_isRetract : IsRetract boool := by
  apply graph_ext
  intro u
  rw [boool_app, boool_app, boool_idem]

end DomainTheory.DataTypesAsLattices
