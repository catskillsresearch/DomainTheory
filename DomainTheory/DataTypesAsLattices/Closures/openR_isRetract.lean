/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.openR_app
public import DomainTheory.DataTypesAsLattices.Closures.openR_idem

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem openR_isRetract : IsRetract openR := by
  change openR = graph (fun x => funOf openR (funOf openR x))
  apply graph_ext
  intro u
  rw [← openR_app]
  exact (openR_idem u).symm

end DomainTheory.DataTypesAsLattices
