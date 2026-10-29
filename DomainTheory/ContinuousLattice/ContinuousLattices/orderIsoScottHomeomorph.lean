module

public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

noncomputable def orderIsoScottHomeomorph (e : A ≃o B) :
    @Homeomorph A B (@scottTopologicalSpace A latticeA)
      (@scottTopologicalSpace B latticeB) := by
  letI : TopologicalSpace A := @scottTopologicalSpace A latticeA
  letI : TopologicalSpace B := @scottTopologicalSpace B latticeB
  letI : Preorder A := latticeA.toPreorder
  letI : Preorder B := latticeB.toPreorder
  exact {
  toEquiv := e.toEquiv
  continuous_toFun := by
    rw [continuous_def]
    intro U hU
    exact ScottOpen.isOpen_iff.mpr
      (ScottOpen.preimage_orderIso e (ScottOpen.isOpen_iff.mp hU))
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    exact ScottOpen.isOpen_iff.mpr
      (ScottOpen.preimage_orderIso e.symm (ScottOpen.isOpen_iff.mp hU))
  }

end DomainTheory.ContinuousLattice
