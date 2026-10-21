/-ai
When every neighbourhood of the generating system is its master, the zeroth projection relates a set X to a set Y exactly when X is a neighbourhood of the colimit and Y is the master of the colimit.

By the relational description, an intermediate neighbourhood of the generating system equals the generating master. The second set is a neighbourhood of the colimit, so it is contained in the master, and it contains the generating master, so the two are equal. In the other direction the generating master lies between the first set, which is contained in the master of the colimit, and that master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}















































/-- **`ρ₀ = ⊥`** when `{Γ}` is the trivial one-point system: `ρ₀` relates `X` only to the master.
This is where Scott's `{Γ}` (a *one-point* domain) is used. -/
theorem rho_zero_rel (s : Setup.{w}) (hΓ : ∀ X, s.Γ.mem X → X = s.Γ.master)
    {X Y : Set s.Tok} :
    (rho s 0).rel X Y ↔ (colim s).mem X ∧ Y = (colim s).master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcX, hcY, z, hz, _, hzY⟩
    have hzm : z = s.Γ.master := hΓ z hz
    subst hzm
    refine ⟨hcX, Set.Subset.antisymm ((colim s).sub_master hcY) ?_⟩
    rw [colim_master]; exact hzY
  · rintro ⟨hcX, rfl⟩
    refine ⟨hcX, (colim s).master_mem, s.Γ.master, s.Γ.master_mem, ?_, ?_⟩
    · have h := (colim s).sub_master hcX; rwa [colim_master] at h
    · rw [colim_master]

end Theorem614
end DomainTheory.NeighbourhoodSystems
