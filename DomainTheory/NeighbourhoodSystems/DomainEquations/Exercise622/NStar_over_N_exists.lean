/-ai
The solution of the vertical-naturals equation is itself a rooted domain, so the stream equation has a solution over that very domain.

The token fixed point of the vertical-naturals expression supplies a set Γ₁ containing the empty string. The singleton system on Γ₁ therefore has the empty string in its master, and the stream solution theorem applied to that system is the required solution.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NExpr_rooted
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NStar_eq_solution

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

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
end DomainTheory.NeighbourhoodSystems
