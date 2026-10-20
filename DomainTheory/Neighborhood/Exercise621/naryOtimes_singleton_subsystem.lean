/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619PartB
import DomainTheory.Neighborhood.Exercise621.Basic
import DomainTheory.Neighborhood.Exercise621.GExpru2enaryOp_rootedConst


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}






























theorem naryOtimes_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.naryOtimes a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619
end DomainTheory.Neighborhood
