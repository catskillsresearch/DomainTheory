/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example62
public import DomainTheory.Neighborhood.Product
public import DomainTheory.Neighborhood.Exercise619.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}











variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}



























/-- `prodTokNbhd D₀.master D₁.master` is exactly the sum master `{Λ} ∪ 0Δ₀ ∪ 1Δ₁`. -/
theorem prodTokNbhd_master_eq : prodTokNbhd D₀.master D₁.master = sumTokMaster D₀ D₁ := rfl

end Exercise619
end DomainTheory.Neighborhood
