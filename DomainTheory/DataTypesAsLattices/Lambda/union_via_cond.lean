/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.eq_2_15
import DomainTheory.DataTypesAsLattices.Lambda.Kcomb_beta
import DomainTheory.DataTypesAsLattices.Lambda.condC_beta3


namespace DomainTheory.DataTypesAsLattices


































/-- **Scott 1976, (2.15)** as a combinator: `cond(x)(y)(K(0)) = x ∪ y`. -/
theorem union_via_cond (x y : Pomega) :
    funOf (funOf (funOf condC x) y) (funOf Kcomb zeroC) = x ∪ y := by
  rw [condC_beta3, Kcomb_beta]
  exact eq_2_15 x y

end DomainTheory.DataTypesAsLattices
