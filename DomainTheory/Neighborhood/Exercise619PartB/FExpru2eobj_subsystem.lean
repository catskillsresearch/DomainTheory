/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619
import DomainTheory.Neighborhood.Definition613
import DomainTheory.Neighborhood.Exercise213
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise619PartB.Basic
import DomainTheory.Neighborhood.Exercise619PartB.sumTok_subsystem
import DomainTheory.Neighborhood.Exercise619PartB.prodTok_subsystem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}













/-- **`λX. T(X)` is monotone on domains.** Whenever `X ◁ Y` we have `T(X) ◁ T(Y)`. -/
theorem FExpr.obj_subsystem : (T : FExpr) → {X Y : ScottSys} → X.sys ◁ Y.sys →
    (T.obj X).sys ◁ (T.obj Y).sys
  | .const D, _, _, _ => Subsystem.refl D.sys
  | .var, _, _, h => h
  | .sum T₀ T₁, _, _, h => sumTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)
  | .prod T₀ T₁, _, _, h => prodTok_subsystem (T₀.obj_subsystem h) (T₁.obj_subsystem h)

end Exercise619
end DomainTheory.Neighborhood
