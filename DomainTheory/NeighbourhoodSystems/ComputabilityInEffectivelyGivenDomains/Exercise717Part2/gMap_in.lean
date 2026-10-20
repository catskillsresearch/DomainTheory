/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}















/-- **`g(in x) = u(x)`.** The injection summand of `D^§ ≅ D + (D^§×D^§)` folds via `u`. -/
theorem gMap_in (hD : ∀ X, D.mem X → X.Nonempty) (x : D.Element) :
    (gMap u v hD).toElementMap (inSharp D hD x) = u.toElementMap x := by
  apply Element.ext
  intro Z
  simp only [mem_toElementMap, gMap_rel]
  constructor
  · rintro ⟨W, hWmem, hrel⟩
    rcases hWmem with rfl | ⟨X, hXx, rfl⟩
    · have hZ := gRel_gamma_inv hD hrel; subst hZ
      exact ⟨D.master, x.master_mem, u.master_rel⟩
    · exact ⟨X, hXx, gRel_embZero_inv hD hrel⟩
  · rintro ⟨X, hXx, hrel⟩
    exact ⟨embZero X, Or.inr ⟨X, hXx, rfl⟩, GRel.leaf hrel⟩

end Exercise717
end DomainTheory.NeighbourhoodSystems
