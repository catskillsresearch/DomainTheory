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
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_iff
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_graph_isClosure

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem eq_5_19 (a : Pomega) :
    funOf Vcomb (funOf Vcomb a) = funOf Vcomb a := by
  have hcl := Vapply_graph_isClosure a
  have hfix := (theorem_5_5_iff (graph (fun x => Vapply a x))).mp hcl
  have ha : funOf Vcomb a = graph (fun x => Vapply a x) := Vcomb_app a
  rw [ha]
  exact hfix

end DomainTheory.DataTypesAsLattices
