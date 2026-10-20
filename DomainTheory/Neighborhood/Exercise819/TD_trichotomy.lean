/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise326Sum
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise819.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u





/-- **`T`'s elements, named via `Example23`.** The three-way classification of `Example12`,
restated with `Example23`'s `⊥`/`true`/`false` names (they are the *same* terms by `rfl`). -/
theorem TD_trichotomy (t : TD.Element) :
    t = Example23.botElt ∨ t = Example23.trueElt ∨ t = Example23.falseElt :=
  Example12.neighborhoodSystem.element_classification t

end DomainTheory.Neighborhood
