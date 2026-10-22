/-ai
The tower retraction at level n+1 sends the conjugate of a Scott map f on D_∞ by the level-(n+1) projection and embedding to the conjugate of f by the level-n projection and embedding.

Extensionality of Scott maps reduces the equality to an evaluation at an arbitrary y. The successor formula for the inverse-limit embedding rewrites the argument of f, and the inverse-limit coherence of the resulting value identifies the retracted (n+1)-st component with the n-th component.
ai-/
module

public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.CLat
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst5
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerType_zero
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.BasicInst8
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerToMap_coe
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.towerProj
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.DInfFn
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.iInfTerm_apply
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.jInfTerm_apply

@[expose] public section

namespace DomainTheory.ContinuousLattice


attribute [instance] CLat.str

section LimitMaps

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

section Thm44b

variable (D₀ : CLat.{u})
  (j₀ : IsContinuousLatticeProjection D₀.carrier (ScottMap D₀.carrier D₀.carrier))

/-- **Step 1 (Lemma-4.5 recursion).** `j_{n+1}(j_{∞(n+1)} ∘ f ∘ i_{(n+1)∞}) = j_{∞n} ∘ f ∘ i_{n∞}`.
This is the equality counterpart of `conjMap_incl_le_conjMap_succ`; it is the hypothesis Lemma 4.5
needs to recognize `j_∞(f)` from its restrictions. -/
theorem towerProj_retr_conjMap_succ (n : ℕ) (f : DInfFn D₀ j₀) :
    (towerProj D₀ j₀ (n + 1)).retr
        (conjMap (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1))
                 (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)) f)
      = conjMap (projInf (towerType D₀) (towerProj D₀ j₀) n)
                (embInf (towerType D₀) (towerProj D₀ j₀) n) f := by
  apply ScottMap.ext
  intro y
  show (towerProj D₀ j₀ n).retr
      (projInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
        (f (embInf (towerType D₀) (towerProj D₀ j₀) (n + 1)
          ((towerProj D₀ j₀ n).incl y))))
    = projInf (towerType D₀) (towerProj D₀ j₀) n
        (f (embInf (towerType D₀) (towerProj D₀ j₀) n y))
  rw [embInf_succ (towerType D₀) (towerProj D₀ j₀) n y]
  exact (f (embInf (towerType D₀) (towerProj D₀ j₀) n y)).2 n

end Thm44b

end LimitMaps

end DomainTheory.ContinuousLattice
