/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise419
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise516.Basic
import DomainTheory.Neighborhood.Exercise516.map_ext_C
import DomainTheory.Neighborhood.Exercise516.mergeElem_diag
import DomainTheory.Neighborhood.Exercise516.mergeMap_pair


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}











































/-- **Exercise 5.16 (Scott 1981, PRG-19).** `merge(x, x) = d(x)` for all `x ∈ |C|` (the doubling map
of Example 4.4). -/
theorem mergeMap_diag (x : C.Element) :
    mergeMap.toElementMap (pair x x) = dMap.toElementMap x := by
  have key : mergeMap.comp (paired (idMap C) (idMap C)) = dMap := by
    apply map_ext_C
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strBot σ) (strBot σ) = pair (shapeElem false σ) (shapeElem false σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_false, dMap_strBot]
    · intro σ
      rw [toElementMap_comp, toElementMap_paired, toElementMap_idMap,
        show pair (strElem σ) (strElem σ) = pair (shapeElem true σ) (shapeElem true σ) from rfl,
        mergeMap_pair, mergeElem_diag, shapeElem_true, dMap_strElem]
  have hx := congrArg (fun m : ApproximableMap C C => m.toElementMap x) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_idMap] at hx
  exact hx

end DomainTheory.Neighborhood.Exercise516
