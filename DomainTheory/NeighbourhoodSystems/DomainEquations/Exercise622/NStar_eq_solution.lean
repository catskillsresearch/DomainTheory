/-ai
If the empty string belongs to the master of a datum domain N, then N* congruent to N ⊕ (N ⊗ N*) has a solution: some nonempty set Γ of strings has its singleton system as a subsystem of the stream expression on N applied to that singleton system. This is the domain of strict streams over N.

The general singleton-subsystem solution applies to the stream expression, using the rootedness lemma for that expression.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NStarExpr_rooted

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- **`N* ≅ N ⊕ (N ⊗ N*)` has a solution** for any rooted datum domain `N` (the strict streams over
`N`). -/
theorem NStar_eq_solution (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem (NStarExpr N) (NStarExpr_rooted hN)

end Exercise619
end DomainTheory.NeighbourhoodSystems
