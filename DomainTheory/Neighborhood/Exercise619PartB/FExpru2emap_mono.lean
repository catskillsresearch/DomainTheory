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
import DomainTheory.Neighborhood.Exercise619PartB.sumMapTok_mono
import DomainTheory.Neighborhood.Exercise619PartB.prodMapTok_mono


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}












/-- **`λf. T(f)` is monotone.** A sharper map `f ≤ f'` is sent to a sharper image `T(f) ≤ T(f')` —
the monotonicity half of *continuous on maps*. -/
theorem FExpr.map_mono : (T : FExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum T₀ T₁, _, _, _, _, h => sumMapTok_mono (T₀.map_mono h) (T₁.map_mono h)
  | .prod T₀ T₁, _, _, _, _, h => prodMapTok_mono (T₀.map_mono h) (T₁.map_mono h)

end Exercise619
end DomainTheory.Neighborhood
