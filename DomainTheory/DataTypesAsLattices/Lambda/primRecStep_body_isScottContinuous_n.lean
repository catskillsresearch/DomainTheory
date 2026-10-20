/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem primRecStep_body_isScottContinuous_n (a f u : Pomega) :
    IsScottContinuous (fun n =>
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n)))) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left a y)
    (fun n => condSet_isScottContinuous_right n a)
    id_isScottContinuous
    (theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun x => funOf_isScottContinuous x)
      (theorem_1_3 (funOf_isScottContinuous f) predSet_isScottContinuous)
      (theorem_1_3 (funOf_isScottContinuous u) predSet_isScottContinuous))

end DomainTheory.DataTypesAsLattices
