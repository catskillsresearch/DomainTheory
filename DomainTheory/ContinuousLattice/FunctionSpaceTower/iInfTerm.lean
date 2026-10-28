module

public import DomainTheory.ContinuousLattice.InverseLimits.embInf
public import DomainTheory.ContinuousLattice.InverseLimits.projInf
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn

@[expose] public section

namespace DomainTheory.ContinuousLattice

attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

noncomputable def iInfTerm (n : ℕ) : ScottMap (DInf D₀ j₀) (DInfFn D₀ j₀) :=
  (conjMap (embInf (towerType D₀) (towerProj D₀ j₀) n)
           (projInf (towerType D₀) (towerProj D₀ j₀) n)).comp
    (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1))

namespace iInfTerm

@[simp] theorem apply (n : ℕ) (x z : DInf D₀ j₀) :
    (iInfTerm D₀ j₀ n x) z
      = embInf (towerType D₀) (towerProj D₀ j₀) n
          ((x.1 (n + 1)) ((projInf (towerType D₀) (towerProj D₀ j₀) n) z)) := rfl

end iInfTerm

end LimitMaps

end DomainTheory.ContinuousLattice
