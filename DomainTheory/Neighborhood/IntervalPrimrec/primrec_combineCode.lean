/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition87
public import DomainTheory.Neighborhood.RationalPrimrec
public import DomainTheory.Neighborhood.RecursiveCross
public import DomainTheory.Neighborhood.IntervalPrimrec.Basic
public import DomainTheory.Neighborhood.IntervalPrimrec.primrec_qpCombineBop

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive











theorem primrec_combineCode : Nat.Primrec (fun t => combineCode t.unpair.1 t.unpair.2) :=
  primrec_crossCombine primrec_qpCombineBop

end DomainTheory.Neighborhood
