module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iSupRho_eq_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.gcomp_rho_indep

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}
















































/-- **The underlying maps of two strict homomorphisms coincide**: `g = g ∘ I = g ∘ ⋃ₙ ρₙ =
⋃ₙ (g ∘ ρₙ)`, and the latter is `g`-independent. -/
theorem gcomp_eq (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) (g g' : AlgHom (colimAlg s) B)
    (hg : IsStrict g.hom) (hg' : IsStrict g'.hom) :
    g.hom = g'.hom := by
  have key : g.hom.comp (iSupRho s) = g'.hom.comp (iSupRho s) := by
    apply ApproximableMap.ext
    intro X Z
    rw [comp_rel, comp_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
    · rintro ⟨Y, ⟨n, hrho⟩, hgYZ⟩
      have hin : (g'.hom.comp (rho s n)).rel X Z := ⟨Y, hrho, hgYZ⟩
      rw [← gcomp_rho_indep s hΓ B g g' hg hg' n] at hin
      obtain ⟨Y', hrho', hgYZ'⟩ := hin
      exact ⟨Y', ⟨n, hrho'⟩, hgYZ'⟩
  have e : g.hom.comp (idMap (colim s)) = g.hom := comp_idMap g.hom
  have e' : g'.hom.comp (idMap (colim s)) = g'.hom := comp_idMap g'.hom
  rw [← e, ← e', ← iSupRho_eq_id]
  exact key

end Theorem614
end DomainTheory.NeighbourhoodSystems
