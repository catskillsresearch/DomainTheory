/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example23
public import DomainTheory.Neighborhood.Exercise316
public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.Exercise317.Basic
public import DomainTheory.Neighborhood.Exercise317.gf_eq_id

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise317

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB ApproximableMap




















/-- **`f` is one-one.** Since `g ∘ f = I_B`, the elementwise map of `f` is injective. -/
theorem f_injective : Function.Injective f.toElementMap := by
  intro x y hxy
  have : (g.comp f).toElementMap x = (g.comp f).toElementMap y := by
    rw [toElementMap_comp, toElementMap_comp, hxy]
  rwa [gf_eq_id, toElementMap_idMap, toElementMap_idMap] at this

end DomainTheory.Neighborhood.Exercise317
