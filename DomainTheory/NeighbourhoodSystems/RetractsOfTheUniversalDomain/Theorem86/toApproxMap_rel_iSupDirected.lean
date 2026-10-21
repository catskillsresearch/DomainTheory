/-ai
The approximable map extracted from a directed supremum of function-space elements relates two neighbourhoods exactly when the map extracted from some stage does.

Both sides rewrite as membership of the output neighbourhood in the directed supremum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- Directed unions of filters correspond, under `toApproxMap`, to the raw (pointwise) union of the
underlying maps' relations — immediate from `mem_iSupDirected` unfolded through `toApproxMap_rel`.
No consistency/directedness argument is needed for this direction. -/
theorem toApproxMap_rel_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (toApproxMap (iSupDirected φ hdir)).rel X Z ↔ ∃ i, (toApproxMap (φ i)).rel X Z := by
  simp only [toApproxMap_rel, mem_iSupDirected]

end Sub8_6

end DomainTheory.NeighbourhoodSystems
