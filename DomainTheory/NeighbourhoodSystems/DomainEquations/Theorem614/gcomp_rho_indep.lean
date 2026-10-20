module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.gcomp_rho_zero_indep
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.gcomp_rho_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}















































/-- **`g`-independence of `gₙ = g ∘ ρₙ`.** For any two strict homomorphisms into the same algebra,
`g ∘ ρₙ = g' ∘ ρₙ` for all `n` — the sequence is determined by the recursion, not by `g`. -/
theorem gcomp_rho_indep (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) (n : ℕ) :
    g.hom.comp (rho s n) = g'.hom.comp (rho s n) := by
  induction n with
  | zero => exact gcomp_rho_zero_indep s hΓ B hg hg'
  | succ k ih => rw [gcomp_rho_succ s B g k, gcomp_rho_succ s B g' k, ih]

end Theorem614
end DomainTheory.NeighbourhoodSystems
