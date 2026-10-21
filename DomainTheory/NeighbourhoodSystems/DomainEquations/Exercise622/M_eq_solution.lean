/-ai
The equation M congruent to {{Λ}} + M has a solution: some nonempty set Γ of strings has its singleton system as a subsystem of the lazy-naturals expression applied to that singleton system. This is the domain of lazy natural numbers.

The general singleton-subsystem solution applies to the lazy-naturals expression, using that the expression is rooted.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.MExpr_rooted

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619









/-- **`M ≅ {{Λ}} + M` has a solution** (the lazy naturals). -/
theorem M_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (MExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem MExpr MExpr_rooted

end Exercise619
end DomainTheory.NeighbourhoodSystems
