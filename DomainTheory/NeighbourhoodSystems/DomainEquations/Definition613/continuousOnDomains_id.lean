/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Definition68
public import DomainTheory.Neighborhood.Proposition611
public import DomainTheory.Neighborhood.Proposition612
public import DomainTheory.Neighborhood.Definition613.Basic
public import DomainTheory.Neighborhood.Definition613.monotoneOnDomains_id

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

universe w







/-- The **identity functor is continuous on domains**: `targetFam` reduces to the plain neighbourhood
family, so directed-union preservation is exactly the hypothesis `hU` that `U` is the union. -/
theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_iUnion, exists_prop]
  exact hU Y

end DomainTheory.Neighborhood
