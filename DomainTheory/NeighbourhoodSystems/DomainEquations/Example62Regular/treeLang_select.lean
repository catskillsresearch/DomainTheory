/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.MyhillNerode
import all Mathlib.Computability.MyhillNerode
public import DomainTheory.Neighborhood.Example62Regular.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

namespace Example62Regular

open Language

variable {n : ℕ}










/-- **The subtree is the left quotient.** `L_{aσ} = σ⁻¹ L_a`: the language of the subtree reached by
reading `σ` is exactly the *left quotient* of `L_a` by `σ` (the residual / "state after reading
`σ`"). This is the heart of Scott's "`a` is the initial state, `aσ` the state after reading `σ`". -/
theorem treeLang_select (a : Tree n) (σ : List (Fin n)) :
    treeLang (select a σ) = (treeLang a).leftQuotient σ := by
  ext τ
  simp only [mem_treeLang, select_apply, Language.mem_leftQuotient]

end Example62Regular
end DomainTheory.Neighborhood
