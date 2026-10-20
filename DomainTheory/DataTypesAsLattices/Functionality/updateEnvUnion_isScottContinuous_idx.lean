/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






































theorem updateEnvUnion_isScottContinuous_idx (t x : Pomega) :
    IsScottContinuous (updateEnvUnion t x) :=
  minExtend_isScottContinuous (fun n => updateEnv t x n)

end DomainTheory.DataTypesAsLattices
