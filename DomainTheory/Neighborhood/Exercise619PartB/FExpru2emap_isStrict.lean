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
import DomainTheory.Neighborhood.Exercise619PartB.sumMapTok_isStrict
import DomainTheory.Neighborhood.Exercise619PartB.prodMapTok_isStrict


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}











/-- **Every `T` preserves strictness** (so it restricts to Scott's category of strict maps): `T(f)`
is strict whenever `f` is (and constants/sums are strict unconditionally). -/
theorem FExpr.map_isStrict : (T : FExpr) → {X Y : ScottSys} → (f : ApproximableMap X.sys Y.sys) →
    IsStrict f → IsStrict (T.map f)
  | .const _, _, _, _, _ => isStrict_idMap
  | .var, _, _, _, hf => hf
  | .sum T₀ T₁, _, _, f, _ => sumMapTok_isStrict (T₀.map f) (T₁.map f)
  | .prod T₀ T₁, _, _, f, hf =>
      prodMapTok_isStrict (T₀.map_isStrict f hf) (T₁.map_isStrict f hf)

end Exercise619
end DomainTheory.Neighborhood
