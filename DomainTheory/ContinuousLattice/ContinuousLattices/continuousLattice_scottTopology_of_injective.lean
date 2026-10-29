module

public import DomainTheory.ContinuousLattice.ContinuousLattices.injective_homeomorph_to_continuousLatticeScott
public import DomainTheory.ContinuousLattice.ContinuousLattices.orderIsoScottHomeomorph
public import DomainTheory.ContinuousLattice.Specialization.SpecializationPreorder

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

/-- If specialization equals a given complete-lattice order on an injective `T₀` space, that
lattice is continuous and the given topology is its Scott topology. -/
theorem continuousLattice_scottTopology_of_injective {A : Type u}
    [latticeA : CompleteLattice A] [τA : TopologicalSpace A]
    [T0Space A] (hA : InjectiveSpace.{u, u} A)
    (hspec : ∀ x y : A, SpecializationPreorder x y ↔ @LE.le A latticeA.toLE x y) :
    ContinuousLattice A ∧
      (@scottTopologicalSpace A latticeA) = τA := by
  obtain ⟨E, instE, hE, ⟨h⟩⟩ := injective_homeomorph_to_continuousLatticeScott hA
  let : CompleteLattice E := instE
  let : TopologicalSpace E := @scottTopologicalSpace E instE
  let : Preorder A := latticeA.toPreorder
  let : Preorder E := instE.toPreorder
  let e : A ≃o E := h.toEquiv.toOrderIso
    (fun x y hxy => by
      exact SpecializationPreorder.scott_iff.mp
        (SpecializationPreorder.map ((hspec x y).mpr hxy) h.continuous))
    (fun x y hxy => by
      exact (hspec (h.symm x) (h.symm y)).mp
        (SpecializationPreorder.map (SpecializationPreorder.scott_iff.mpr hxy) h.symm.continuous))
  have hcont : ContinuousLattice A := ContinuousLattice.orderIso e hE
  refine ⟨hcont, ?_⟩
  have heqOrder :
      (@scottTopologicalSpace A latticeA) =
        TopologicalSpace.induced (e : A → E) (@scottTopologicalSpace E instE) := by
    let : TopologicalSpace A := @scottTopologicalSpace A latticeA
    exact (@orderIsoScottHomeomorph A E latticeA instE e).isInducing.eq_induced
  have heqHome :
      τA = TopologicalSpace.induced (h : A → E) (@scottTopologicalSpace E instE) :=
    (@Homeomorph.isInducing A E τA (@scottTopologicalSpace E instE) h).eq_induced
  exact heqOrder.trans heqHome.symm

end DomainTheory.ContinuousLattice
