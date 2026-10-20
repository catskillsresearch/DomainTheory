/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
public import DomainTheory.DataTypesAsLattices.Retracts.intR_eq_intF
public import DomainTheory.DataTypesAsLattices.Retracts.intR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem intR_isGraph : intR = graph (funOf intR) := by
  refine intR_eq_intF.symm.trans ?_
  apply graph_ext
  intro u
  exact (intR_app u).symm

end DomainTheory.DataTypesAsLattices
