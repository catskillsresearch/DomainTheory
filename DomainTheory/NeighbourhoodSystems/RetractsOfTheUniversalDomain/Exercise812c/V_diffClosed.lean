/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812
public import DomainTheory.Neighborhood.IntervalPrimrec
public import DomainTheory.Neighborhood.Theorem88
public import DomainTheory.Neighborhood.Exercise812c.Basic
public import DomainTheory.Neighborhood.Exercise812c.V_diff_mem

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem







theorem V_diffClosed : V.DiffClosed := fun hX hY => V_diff_mem hX hY

end DomainTheory.Neighborhood
