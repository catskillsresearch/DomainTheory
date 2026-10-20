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
public import DomainTheory.Neighborhood.Exercise821.aSharp_le_idMap_of_le
public import DomainTheory.Neighborhood.Exercise821.aSharpInner_idem_of_isRetraction
public import DomainTheory.Neighborhood.Exercise821.isRetraction_aSharp

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}












/-- **Exercise 8.21(b), assembled.** `a` a projection of `U` `⟹` `a§` a projection: the `≤ I` half
is 8.21(a)'s `aSharp_le_idMap_of_le`; the retraction half chains `aSharpInner_idem_of_isRetraction`
(the `gMap`-level idempotence, via the catamorphism-uniqueness lemma `gMap_eq_of_satisfies`) with
`isRetraction_aSharp` (transport through `U§ ⊴ U`). This completes "`a` a projection ⟹ `a§` a
projection" in full, matching `Proposition810.lean`'s `isProjection_sumComb`/`isProjection_prodComb`/
`isProjection_arrowComb`. -/
theorem isProjection_aSharp {a : ApproximableMap U U} (ha : IsProjection a) :
    IsProjection (aSharp a) :=
  ⟨isRetraction_aSharp (aSharpInner_idem_of_isRetraction ha.1), aSharp_le_idMap_of_le ha.2⟩

end DomainTheory.Neighborhood
