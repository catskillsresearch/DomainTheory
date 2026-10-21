/-ai
The equation N congruent to {{0}, {0, Λ}} ⊕ N has a solution: some nonempty set Γ of strings, the token set of the vertical naturals, satisfies Γ = tok of the vertical-naturals expression applied to the singleton system on Γ, so that singleton system is a subsystem of the expression applied to it and Theorem 6.14 applies.

The general singleton-subsystem solution applies to the vertical-naturals expression, using that the expression is rooted.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NExpr_rooted

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- **`N ≅ {{0},{0,Λ}} ⊕ N` has a solution.** There is `Γ` (the vertical naturals' token set) with
`Γ = tok(NExpr({Γ}))`, so `{Γ} ◁ NExpr({Γ})` and Theorem 6.14 applies. -/
theorem N_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (NExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem NExpr NExpr_rooted

end Exercise619
end DomainTheory.NeighbourhoodSystems
