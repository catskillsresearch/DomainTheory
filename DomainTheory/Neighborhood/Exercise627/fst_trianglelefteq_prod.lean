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
public import DomainTheory.Neighborhood.Exercise627.fstProj_comp_fstInj
public import DomainTheory.Neighborhood.Exercise627.fstInj_comp_fstProj_le

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}





/-- **Exercise 6.27 (2).** `𝒟 ⊴ 𝒟 × ℰ`. -/
theorem fst_trianglelefteq_prod (D₀ D₁ : NeighborhoodSystem Str) :
    D₀ ⊴ prodTok D₀ D₁ :=
  trianglelefteq_of_projectionPair (fstInj D₀ D₁) (fstProj D₀ D₁)
    (fstProj_comp_fstInj D₀ D₁) (fstInj_comp_fstProj_le D₀ D₁)

end Exercise627
end DomainTheory.Neighborhood
