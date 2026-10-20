/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- `i` occurs anywhere in `t` (free or bound). Freshness for (α). -/
def Occurs (i : ℕ) : Term → Prop
  | .var j => j = i
  | .zero => False
  | .succ t => Occurs i t
  | .pred t => Occurs i t
  | .cond z x y => Occurs i z ∨ Occurs i x ∨ Occurs i y
  | .app u x => Occurs i u ∨ Occurs i x
  | .lam k body => k = i ∨ Occurs i body

end DomainTheory.DataTypesAsLattices
