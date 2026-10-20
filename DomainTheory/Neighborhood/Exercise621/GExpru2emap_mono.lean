/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise619PartB
import DomainTheory.Neighborhood.Exercise621.Basic
import DomainTheory.Neighborhood.Exercise621.oplusMapTok_mono
import DomainTheory.Neighborhood.Exercise621.otimesMapTok_mono


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}




variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}














variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}








/-- **`λf. T(f)` is monotone** (the order half of *continuous on maps*). -/
theorem GExpr.map_mono : (T : GExpr) → {X Y : ScottSys} → {f f' : ApproximableMap X.sys Y.sys} →
    f ≤ f' → T.map f ≤ T.map f'
  | .const _, _, _, _, _, _ => le_rfl
  | .var, _, _, _, _, h => h
  | .sum a b, _, _, _, _, h => sumMapTok_mono (a.map_mono h) (b.map_mono h)
  | .prod a b, _, _, _, _, h => prodMapTok_mono (a.map_mono h) (b.map_mono h)
  | .oplus a b, _, _, _, _, h => oplusMapTok_mono (a.map_mono h) (b.map_mono h)
  | .otimes a b, _, _, _, _, h => otimesMapTok_mono (a.map_mono h) (b.map_mono h)

end Exercise619
end DomainTheory.Neighborhood
