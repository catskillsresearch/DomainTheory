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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gRel_dom
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.embZero_ne_embPair_of_memS

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Inversion at a node `1·P ∪ 2·Q`: `(1·P∪2·Q) g Z ↔ ∃ Z₁ Z₂, P g Z₁ ∧ Q g Z₂ ∧ ⟨Z₁,Z₂⟩ v Z`. -/
theorem gRel_embPair_inv (hD : ∀ X, D.mem X → X.Nonempty) {P Q : Set (List Bool × α)} {Z}
    (h : GRel u v (embPair P Q) Z) :
    ∃ Z₁ Z₂, GRel u v P Z₁ ∧ GRel u v Q Z₂ ∧ v.rel (prodNbhd Z₁ Z₂) Z := by
  have hPQ := gRel_dom h
  obtain ⟨hPmem, hQmem⟩ := memS_embPair_inv hD hPQ
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma hZ => exact absurd hW (embPair_ne_Gamma D hD P Q)
  | @leaf X Z hrel => exact absurd hW.symm (embZero_ne_embPair_of_memS hD hPmem)
  | @node P' Q' Z₁ Z₂ Z hP' hQ' hvrel =>
      obtain ⟨rfl, rfl⟩ := embPair_injective hW
      exact ⟨Z₁, Z₂, hP', hQ', hvrel⟩

end Exercise717

end DomainTheory.NeighbourhoodSystems
