/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem condC_beta2 (x y : Pomega) :
    funOf (funOf condC x) y = graph (fun z => condSet z x y) := by
  rw [condC_beta]
  exact beta (graph_const_isScottContinuous (fun y z => condSet z x y)
    (fun z => condSet_isScottContinuous_right z x)) y

end DomainTheory.DataTypesAsLattices
