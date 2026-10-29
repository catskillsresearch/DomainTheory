module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

structure retraction (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] where
  incl : ScottMap D₀ D₁ → ScottMap D₀' D₁'
  retr : ScottMap D₀' D₁' → ScottMap D₀ D₁
  retr_incl : ∀ f, retr (incl f) = f

namespace retraction

def functionSpace (R₀ : IsContinuousLatticeRetraction D₀ D₀') (R₁ : IsContinuousLatticeRetraction D₁ D₁') :
    ScottMap.retraction D₀ D₀' D₁ D₁' where
  incl f := ScottMap.comp R₁.incl (ScottMap.comp f R₀.retr)
  retr f' := ScottMap.comp R₁.retr (ScottMap.comp f' R₀.incl)
  retr_incl f := ScottMap.ext fun x => by simp [ScottMap.comp, R₀.retr_incl, R₁.retr_incl]

end retraction

structure projection (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] extends
    ScottMap.retraction D₀ D₀' D₁ D₁' where
  incl_retr_le : ∀ f' x, (incl (retr f')) x ≤ f' x

namespace projection

def functionSpace (P₀ : IsContinuousLatticeProjection D₀ D₀') (P₁ : IsContinuousLatticeProjection D₁ D₁') :
    ScottMap.projection D₀ D₀' D₁ D₁' :=
  ScottMap.projection.mk
    (ScottMap.retraction.functionSpace P₀.toIsContinuousLatticeRetraction P₁.toIsContinuousLatticeRetraction)
    (by
      intro f' y
      dsimp only [ScottMap.retraction.functionSpace, ScottMap.comp, Function.comp_def]
      exact le_trans (P₁.incl_retr_le (f' (P₀.incl (P₀.retr y))))
        (ScottMap.monotone f' (P₀.incl_retr_le y)))

end projection

end ScottMap

end DomainTheory.ContinuousLattice
