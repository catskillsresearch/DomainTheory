/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example44
import DomainTheory.Neighborhood.Exercise326
import DomainTheory.Neighborhood.Exercise419.Basic


namespace DomainTheory.Neighborhood.Exercise419

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44






variable {β : Type*}


















/-- **Exercise 4.19 (Scott 1981, PRG-19).** `one` is definable from `empty`, `zero`, `cond`: the
equation `one(x) = cond(empty(x), false, cond(zero(x), false, true))` holds on every total element
`σ`. -/
theorem one_def_strElem (σ : Str) : oneMap.toElementMap (strElem σ) = oneDef (strElem σ) := by
  cases σ with
  | nil =>
    -- empty(Λ)=true ⟹ cond picks `false`
    rw [oneDef, emptyMap_strElem, headValC_nil, Exercise326.cond_true,
      oneMap_strElem, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      -- empty=false ⟹ inner cond; zero(0σ)=true ⟹ inner cond picks `false`
      rw [oneDef, emptyMap_strElem, headValC_false, Exercise326.cond_false,
        zeroMap_strElem, headValC_false, Exercise326.cond_true, oneMap_strElem, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strElem, headValC_true, Exercise326.cond_false,
        zeroMap_strElem, headValC_true, Exercise326.cond_false, oneMap_strElem, headValC_true]

end DomainTheory.Neighborhood.Exercise419
