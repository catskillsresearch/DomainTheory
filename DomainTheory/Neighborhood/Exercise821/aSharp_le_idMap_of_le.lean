/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise717Part2
import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Proposition810
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise821.Basic
import DomainTheory.Neighborhood.Exercise821.gMap_mono
import DomainTheory.Neighborhood.Exercise821.iSharp_comp_jSharp_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}











/-- **`a ≤ I ⟹ a§ ≤ I`** (half of "`a` a projection ⟹ `a§` a projection", Proposition 8.10's
proof recipe transcribed to `§`). -/
theorem aSharp_le_idMap_of_le {a : ApproximableMap U U} (ha : a ≤ idMap U) :
    aSharp a ≤ idMap U := by
  have h1 : (inSharpMap U_mem_nonempty).comp a ≤ inSharpMap U_mem_nonempty := by
    calc (inSharpMap U_mem_nonempty).comp a
        ≤ (inSharpMap U_mem_nonempty).comp (idMap U) := comp_mono_gen le_rfl ha
      _ = inSharpMap U_mem_nonempty := comp_idMap _
  have h2 : aSharpInner a ≤ idMap (Dsharp U U_mem_nonempty) := by
    calc aSharpInner a
        ≤ gMap (inSharpMap U_mem_nonempty) (pairSharpMap U_mem_nonempty) U_mem_nonempty :=
          gMap_mono U_mem_nonempty h1 le_rfl
      _ = idMap (Dsharp U U_mem_nonempty) := gMap_inSharp_pairSharp_eq_idMap
  calc aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := aSharp_eq a
    _ ≤ iSharp.comp ((idMap (Dsharp U U_mem_nonempty)).comp jSharp) :=
        comp_mono_gen le_rfl (comp_mono_gen h2 le_rfl)
    _ = iSharp.comp jSharp := by rw [idMap_comp]
    _ ≤ idMap U := iSharp_comp_jSharp_le

end DomainTheory.Neighborhood
