/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise621
public import DomainTheory.Neighborhood.Exercise622.Basic
public import DomainTheory.Neighborhood.Exercise622.NExpr_rooted
public import DomainTheory.Neighborhood.Exercise622.NStar_eq_solution

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB

namespace Exercise619









/-- **Chaining the equations.** The solution `N` to the first equation is itself a rooted domain
(`Λ ∈ tok(N)`, since its token set is the fixed point `Γ₁ ∋ Λ`), so it is a legitimate datum domain
for the third: `N*` exists *over the very `N` produced by* `N ≅ {{0},{0,Λ}} ⊕ N`. -/
theorem NStar_over_N_exists :
    ∃ N : ScottSys, ([] : Str) ∈ N.sys.master ∧
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ₁, hnil₁, _⟩ := gExists_tok_fixedPoint NExpr NExpr_rooted
  exact ⟨singletonSys Γ₁ ⟨[], hnil₁⟩, hnil₁, NStar_eq_solution _ hnil₁⟩

end Exercise619
end DomainTheory.Neighborhood
