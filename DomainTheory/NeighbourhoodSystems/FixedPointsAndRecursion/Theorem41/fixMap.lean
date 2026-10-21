/-ai
The fixed-point operator of a neighbourhood system is the approximable map from its function space obtained by extending the assignment that sends each function-space neighbourhood to the least fixed point of the least approximable map of the corresponding principal element. That assignment is monotone because a contained neighbourhood determines a larger principal element, the function-space equivalence preserves the order, and the least fixed point is monotone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

open ApproximableMap

/-- **Theorem 4.2 (Scott 1981, PRG-19).** The fixed-point operator `fix : (𝒟 → 𝒟) → 𝒟` as an
approximable mapping. Built by the extension principle (Exercise 2.8, `ofMono`): on the finite
element `↑F` it returns `fix(↑F)`, where `↑F = toApproxMap (principal hF)` is the least map of the
neighbourhood `F` (Proposition 3.9). Monotonicity of `↑F ↦ fix(↑F)` is `fixElement_mono` composed
with the order-iso `funSpaceEquiv`. -/
def fixMap (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V :=
  ofMono (fun W hW => (toApproxMap ((funSpace V V).principal hW)).fixElement)
    (fun W W' hW hW' hW'W => by
      apply fixElement_mono
      exact (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff hW hW').mpr hW'W))

end DomainTheory.NeighbourhoodSystems
