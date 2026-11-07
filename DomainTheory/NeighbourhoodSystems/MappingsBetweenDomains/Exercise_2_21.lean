module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.C

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem BitDom
open DomainTheory.NeighbourhoodSystems
open C
/-- Scott's Exercise 2.21: system `C` has finite totals strictly above `⊥`, juxtaposition is
    left-biased on cones, and on total finite left arguments it prepends neighbourhoods of the
    right argument. -/
theorem example_221 :
    (C.bot < Lambda) ∧
    (∀ σ, C.IsTotal (singletonElt σ)) ∧
    (∀ σ y, juxtapose.toElementMap₂ (C.principal (memC_cone σ)) y =
      C.principal (memC_cone σ)) ∧
    (∀ σ y {Z}, (juxtapose.toElementMap₂ (singletonElt σ) y).mem Z ↔
      C.mem Z ∧ ∃ Y', y.mem Y' ∧ prepend σ Y' ⊆ Z) :=
  ⟨bot_lt_Lambda, isTotal_singletonElt, juxtapose_cone, juxtapose_singleton_mem⟩
