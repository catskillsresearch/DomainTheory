/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition613
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem614.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

universe w

namespace Theorem614


variable {α : Type w}










































/-- In the category of domains, `⊚` (categorical composition) is `ApproximableMap.comp`. -/
theorem cat_comp_eq {X Y Z : DomainObj} (g : Category.Hom Y Z) (f : Category.Hom X Y) :
    g ⊚ f = g.comp f := rfl

end Theorem614
end DomainTheory.Neighborhood
