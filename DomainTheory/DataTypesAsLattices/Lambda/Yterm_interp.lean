/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


















































theorem Yterm_interp : interp Yterm (fun _ => botElem) = Ycomb := by
  simp [Yterm, interp, Ycomb, omegaComb, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
