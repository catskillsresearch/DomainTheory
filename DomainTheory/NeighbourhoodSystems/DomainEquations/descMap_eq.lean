/-ai
The descent map applied to an element is the directed supremum of the descent chain applied to that element.

Compare neighbourhoods. Membership under the descent map is membership under some stage of the chain, which is membership in the directed supremum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.succChainDir
public import DomainTheory.NeighbourhoodSystems.DomainEquations.descSeqEltMono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

section Target

variable {γ : Type*} {E : NeighborhoodSystem γ}

/-- **The descent map as a directed union.** `h(x) = ⋃ₙ hₙ(x)`. -/
theorem descMap_eq (k : ApproximableMap (prod V E) E) (x : (iterSys V).Element) :
    (descMap k).toElementMap x
      = iSupDirected (fun n => (descSeq k n).toElementMap x)
          (succChainDir _ (descSeqEltMono k x)) := by
  apply Element.ext
  intro Y
  rw [descMap_toElementMap, mem_iSupDirected]

end Target

end Exercise618

end DomainTheory.NeighbourhoodSystems
