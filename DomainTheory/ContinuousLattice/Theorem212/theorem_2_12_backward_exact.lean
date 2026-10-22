/-ai
If an injective T₀ topology on a specified complete lattice has that lattice order as its specialization order, then the lattice is continuous and the given topology is its Scott topology.

The backward direction of Theorem 2.12 supplies a homeomorphism with the Scott topology of some continuous lattice. The homeomorphism is an order isomorphism. In one direction a lattice inequality is Scott specialization, continuous maps preserve specialization, and specialization in the Scott topology of the target is its lattice order. In the other direction the inverse homeomorphism and the specialization hypothesis run the same comparison backwards. Continuous-lattice structure transfers across this order isomorphism. The Scott topology of the source is the topology induced by the order isomorphism from the Scott topology of the target, and the given topology is the topology induced by the homeomorphism from that same Scott topology.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.Basic
public import DomainTheory.ContinuousLattice.Theorem212.theorem_2_12_backward
public import DomainTheory.ContinuousLattice.Theorem212.IsContinuousLatticeu2eorderIso

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set


universe u


section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]


/-- **Theorem 2.12, source-faithful exact-order form.** If an injective `T₀` topology on an
already specified complete lattice has that lattice order as its specialization order, then the
specified lattice is continuous and the given topology is exactly its Scott topology. -/
theorem theorem_2_12_backward_exact [τA : TopologicalSpace A] [T0Space A]
    (hA : InjectiveSpace.{u, u} A)
    (hspec : ∀ x y : A, SpecializationLe x y ↔ @LE.le A latticeA.toLE x y) :
    IsContinuousLattice A ∧
      (@scottTopologicalSpace A latticeA) = τA := by
  obtain ⟨E, instE, hE, ⟨h⟩⟩ := theorem_2_12_backward hA
  let : CompleteLattice E := instE
  let : TopologicalSpace E := @scottTopologicalSpace E instE
  let : Preorder A := latticeA.toPreorder
  let : Preorder E := instE.toPreorder
  let e : A ≃o E := h.toEquiv.toOrderIso
    (fun x y hxy => by
      exact specializationLe_scott_iff.mp
        (SpecializationLe.map ((hspec x y).mpr hxy) h.continuous))
    (fun x y hxy => by
      exact (hspec (h.symm x) (h.symm y)).mp
        (SpecializationLe.map (specializationLe_scott_iff.mpr hxy) h.symm.continuous))
  have hcont : IsContinuousLattice A := IsContinuousLattice.orderIso e hE
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

end Theorem212Transfer
end DomainTheory.ContinuousLattice
