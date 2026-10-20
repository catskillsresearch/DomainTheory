/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.seq2_app_zero


namespace DomainTheory.DataTypesAsLattices



































/-- **Scott 1976, (2.23).** Projection of a binary sequence. -/
theorem eq_2_23_zero (x y : Pomega) : funOf (seq2 x y) (ofNat 0) = x :=
  seq2_app_zero x y

end DomainTheory.DataTypesAsLattices
