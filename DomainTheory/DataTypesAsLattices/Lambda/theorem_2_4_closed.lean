/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_6
public import DomainTheory.DataTypesAsLattices.Lambda.predC_app
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_complete
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb_combinatory

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem theorem_2_4_closed (t : Term) :
    IsCombinatory (interp t (fun _ => botElem)) := by
  rw [theorem_2_4_complete]
  refine ofComb_combinatory _ _ fun _ => ?_
  have hbot : funOf predC zeroC = botElem := by
    rw [predC_app]; exact eq_2_6
  exact hbot ▸ IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end DomainTheory.DataTypesAsLattices
