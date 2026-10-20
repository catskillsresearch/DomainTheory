/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_one


namespace DomainTheory.DataTypesAsLattices



































theorem eq_2_23_one (x y : Pomega) : funOf (seq2 x y) (ofNat 1) = y :=
  seq2_app_one x y

end DomainTheory.DataTypesAsLattices
