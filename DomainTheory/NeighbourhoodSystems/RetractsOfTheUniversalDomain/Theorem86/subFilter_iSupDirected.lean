/-ai
The filter transport of sub preserves directed suprema.

Injectivity of extraction reduces the equality of elements to an equality of maps. The image of the filter transport is sub of the extracted map. Extensionality reduces the equality to relations. The relation of sub of the extracted supremum holds exactly when it holds at some stage, and the relation of the extracted supremum of the transported elements is the same existence after each transported element is rewritten as sub of the extracted stage.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_injective
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_subFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.toApproxMap_rel_iSupDirected
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_toApproxMap_iSupDirected

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`subFilter` preserves directed unions.** Assembled from `sub_toApproxMap_iSupDirected` and
`toApproxMap_rel_iSupDirected` via `toApproxMap`'s injectivity. -/
theorem subFilter_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k)
    (hdir' : ∀ i j, ∃ k, subFilter (φ i) ≤ subFilter (φ k) ∧ subFilter (φ j) ≤ subFilter (φ k)) :
    subFilter (iSupDirected φ hdir) = iSupDirected (fun i => subFilter (φ i)) hdir' := by
  apply toApproxMap_injective
  rw [toApproxMap_subFilter]
  apply ApproximableMap.ext
  intro X Z
  rw [sub_toApproxMap_iSupDirected, toApproxMap_rel_iSupDirected]
  simp only [toApproxMap_subFilter]

end Sub8_6

end DomainTheory.NeighbourhoodSystems
