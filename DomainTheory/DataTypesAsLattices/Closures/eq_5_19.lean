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
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_iff
import DomainTheory.DataTypesAsLattices.Closures.Vapply_graph_isClosure


namespace DomainTheory.DataTypesAsLattices
































theorem eq_5_19 (a : Pomega) :
    funOf Vcomb (funOf Vcomb a) = funOf Vcomb a := by
  have hcl := Vapply_graph_isClosure a
  have hfix := (theorem_5_5_iff (graph (fun x => Vapply a x))).mp hcl
  have ha : funOf Vcomb a = graph (fun x => Vapply a x) := Vcomb_app a
  rw [ha]
  exact hfix

end DomainTheory.DataTypesAsLattices
