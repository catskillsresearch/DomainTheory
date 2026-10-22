module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.gcomp_rho_zero_rel

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}


/-- The base case of `g`-independence: any two strict maps agree after `∘ ρ₀`. -/
theorem gcomp_rho_zero_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g g' : ApproximableMap (colim s) B.carrier.sys}
    (hg : IsStrict g) (hg' : IsStrict g') :
    g.comp (rho s 0) = g'.comp (rho s 0) := by
  apply ApproximableMap.ext
  intro X Z
  rw [gcomp_rho_zero_rel s hΓ B hg, gcomp_rho_zero_rel s hΓ B hg']

end Theorem614
end DomainTheory.NeighbourhoodSystems
