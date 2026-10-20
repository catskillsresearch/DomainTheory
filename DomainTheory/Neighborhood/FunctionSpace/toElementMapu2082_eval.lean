/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

















































variable {V₂ : NeighborhoodSystem γ}


/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(f, x) = f(x)` (with the filter `φ` viewed as
the map `toApproxMap φ` via Theorem 3.10). -/
theorem toElementMap₂_eval (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (eval V₁ V₂).toElementMap₂ φ x = (toApproxMap φ).toElementMap x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨F, X, hφF, hxX, _, hX, hY, hrel⟩
    refine ⟨X, hxX, ?_⟩
    show φ.mem (step X Y)
    exact φ.up_mem hφF (step_mem hX hY) (fun f hf => hrel f hf)
  · rintro ⟨X, hxX, hrel⟩
    have hstep : (funSpace V₁ V₂).mem (step X Y) := φ.sub hrel
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hstep).2
    exact ⟨step X Y, X, hrel, hxX, hstep, f.rel_dom hf, f.rel_cod hf, fun g hg => hg⟩

end DomainTheory.Neighborhood
