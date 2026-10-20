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
import DomainTheory.Neighborhood.Exercise619PartB.sumMapTok_id
import DomainTheory.Neighborhood.Exercise619PartB.prodMapTok_id


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619





variable {A₀ A₁ B₀ B₁ C₀ C₁ : ScottSys}











/-- **Functor law 1 — `T(I_X) = I_{T(X)}`.** Every construct `T` preserves identities. -/
theorem FExpr.map_id : (T : FExpr) → (X : ScottSys) → T.map (idMap X.sys) = idMap (T.obj X).sys
  | .const D, _ => rfl
  | .var, _ => rfl
  | .sum T₀ T₁, X => by
      show sumMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).sum (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, sumMapTok_id]
  | .prod T₀ T₁, X => by
      show prodMapTok (T₀.map (idMap X.sys)) (T₁.map (idMap X.sys))
          = idMap ((T₀.obj X).prod (T₁.obj X)).sys
      rw [T₀.map_id X, T₁.map_id X, prodMapTok_id]

end Exercise619
end DomainTheory.Neighborhood
