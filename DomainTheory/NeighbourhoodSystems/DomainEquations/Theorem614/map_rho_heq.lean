module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.map_comp_proj_heq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614


variable {α : Type w}













































/-- **`T(ρₙ) = ρₙ₊₁`, heterogeneously.** The image `T(ρₙ)` of the `n`-th projection, living over
`T(𝒟)`'s carrier, is heterogeneously equal to the `(n+1)`-st projection `ρₙ₊₁` over `Tok`. -/
theorem map_rho_heq (s : Setup.{w}) (n : ℕ) :
    HEq (Tmap_rho s n) (rho s (n + 1)) := by
  have hcomp : Tmap_rho s n
      = (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj).comp
          (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj) :=
    s.T.map_comp (X := objColim s) (Y := objDsys s n) (Z := objColim s)
      (Dsys_sub_colim s n).inj (Dsys_sub_colim s n).proj
  rw [hcomp]
  exact map_comp_proj_heq (Dceq s n) (colimCeq s) (s.hmono (Dsys_sub_colim s n)).carrier_eq
    (s.hmono (Dsys_sub_colim s n)).sub (Dsys_succ s n).symm (Tcolim_eq_colim s)
    (Dsys_sub_colim s (n + 1)) (s.T.map (X := objDsys s n) (Y := objColim s) (Dsys_sub_colim s n).inj)
    (s.T.map (X := objColim s) (Y := objDsys s n) (Dsys_sub_colim s n).proj)
    (s.hmono (Dsys_sub_colim s n)).inj_heq (s.hmono (Dsys_sub_colim s n)).proj_heq

end Theorem614
end DomainTheory.NeighbourhoodSystems
