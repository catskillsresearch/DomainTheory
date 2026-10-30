module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm
public import DomainTheory.ContinuousLattice.InverseLimits.proposition_4_2
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_7_projection

@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : ContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : ContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

theorem conj_iInfTerm_eq (n : ℕ) (x : DInf D₀ j₀) :
    conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
            (embInf (towerType D₀) (towerProj D₀ j₀) n)
            (iInfTerm D₀ j₀ n x) = x.1 (n + 1) :=
  (proposition_3_7_projection
      (proposition_4_2 (towerType D₀) (towerProj D₀ j₀) n)
      (proposition_4_2 (towerType D₀) (towerProj D₀ j₀) n)).retr_incl
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1) x)

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
