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






















/-- **Exercise 6.19 — *"Are these correct up to isomorphism?"* (sum).** Scott's uniform
`{0,1}*`-presentation `𝒟₀ + 𝒟₁` is isomorphic, as a domain, to the abstract separated sum of
Exercise 3.18. -/
theorem sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁ := ⟨sumTokEquiv⟩

end Exercise619
end DomainTheory.Neighborhood
