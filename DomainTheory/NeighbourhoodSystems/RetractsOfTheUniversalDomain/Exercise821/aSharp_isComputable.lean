/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise717Part2
public import DomainTheory.Neighborhood.Definition89
public import DomainTheory.Neighborhood.Proposition810
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Exercise821.Basic
public import DomainTheory.Neighborhood.Exercise821.iSharp_isComputableMap
public import DomainTheory.Neighborhood.Exercise821.jSharp_isComputableMap

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}











/-- **`a§` is computable whenever `a` is.** -/
theorem aSharp_isComputable {a : ApproximableMap U U}
    (ha : IsComputableMap UComputablePresentation UComputablePresentation a) :
    IsComputableMap UComputablePresentation UComputablePresentation (aSharp a) := by
  have hu : IsComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty)
      ((inSharpMap U_mem_nonempty).comp a) :=
    comp_isComputable ha (inSharp_isComputable U_mem_nonempty UComputablePresentation)
  have hInner : IsComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      (dsharpPresentation UComputablePresentation U_mem_nonempty) (aSharpInner a) :=
    gMap_isComputable U_mem_nonempty UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) hu
      (pairSharp_isComputable U_mem_nonempty UComputablePresentation)
  exact comp_isComputable (comp_isComputable jSharp_isComputableMap hInner) iSharp_isComputableMap

end DomainTheory.Neighborhood
