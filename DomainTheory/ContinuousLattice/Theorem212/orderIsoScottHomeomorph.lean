module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.scottOpen_preimage_orderIso

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

/-- An order isomorphism is a homeomorphism between the corresponding Scott topologies. -/
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
    exact isOpen_iff_scottOpen.mpr
      (scottOpen_preimage_orderIso e (isOpen_iff_scottOpen.mp hU))
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    exact isOpen_iff_scottOpen.mpr
      (scottOpen_preimage_orderIso e.symm (isOpen_iff_scottOpen.mp hU))
  }

end Theorem212Transfer

end DomainTheory.ContinuousLattice
