/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise621
public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Exercise627.Basic
public import DomainTheory.Neighborhood.Exercise627.strictifyMap_of_isStrict
public import DomainTheory.Neighborhood.Exercise627.toApproxMap_toFilter
public import DomainTheory.Neighborhood.Exercise627.toStrictFilter_toStrictMap

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}






variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

















section Part5

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










theorem strct_incl (φ : (strictFun V₀ V₁).Element) : strct (incl φ) = φ := by
  show toStrictFilter (strictify (toApproxMap (toFilter (toStrictMap φ).1))) = φ
  rw [toApproxMap_toFilter,
    show strictify (toStrictMap φ).1 = toStrictMap φ from
      Subtype.ext (strictifyMap_of_isStrict (toStrictMap φ).2)]
  exact toStrictFilter_toStrictMap φ

end Part5
end Exercise627
end DomainTheory.Neighborhood
