module

public import DomainTheory.ContinuousLattice.FunctionSpaces.Projection

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D₀ D₀' D₁ D₁' : Type*}

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace FunctionSpace

def retraction (R₀ : ContinuousLatticeRetraction D₀ D₀') (R₁ : ContinuousLatticeRetraction D₁ D₁') :
    ScottMap.retraction D₀ D₀' D₁ D₁' where
  incl f := ScottMap.comp R₁.incl (ScottMap.comp f R₀.retr)
  retr f' := ScottMap.comp R₁.retr (ScottMap.comp f' R₀.incl)
  retr_incl f := ScottMap.ext fun x => by simp [ScottMap.comp, R₀.retr_incl, R₁.retr_incl]

def projection (P₀ : ContinuousLatticeProjection D₀ D₀') (P₁ : ContinuousLatticeProjection D₁ D₁') :
    ScottMap.projection D₀ D₀' D₁ D₁' :=
  ScottMap.projection.mk
    (FunctionSpace.retraction P₀.toContinuousLatticeRetraction P₁.toContinuousLatticeRetraction)
    (by
      intro f' y
      dsimp only [FunctionSpace.retraction, ScottMap.comp, Function.comp_def]
      exact le_trans (P₁.incl_retr_le (f' (P₀.incl (P₀.retr y))))
        (ScottMap.monotone f' (P₀.incl_retr_le y)))

end FunctionSpace

end DomainTheory.ContinuousLattice
