module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.strict_rel_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho_zero_rel

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}















































/-- For a strict homomorphism `g`, the base `g ∘ ρ₀` is the least map: it relates `X` only to the
master of `E`, independent of `g`. -/
theorem gcomp_rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    (B : TAlgebra s.T) {g : ApproximableMap (colim s) B.carrier.sys} (hg : IsStrict g)
    {X : Set s.Tok} {Z : Set B.carrier.carrier} :
    (g.comp (rho s 0)).rel X Z ↔ (colim s).mem X ∧ Z = B.carrier.sys.master := by
  rw [comp_rel]
  constructor
  · rintro ⟨Y, hrho, hgYZ⟩
    rw [rho_zero_rel s hΓ] at hrho
    obtain ⟨hcX, rfl⟩ := hrho
    exact ⟨hcX, (strict_rel_master hg).mp hgYZ⟩
  · rintro ⟨hcX, rfl⟩
    exact ⟨(colim s).master, (rho_zero_rel s hΓ).mpr ⟨hcX, rfl⟩, g.master_rel⟩

end Theorem614
end DomainTheory.NeighbourhoodSystems
