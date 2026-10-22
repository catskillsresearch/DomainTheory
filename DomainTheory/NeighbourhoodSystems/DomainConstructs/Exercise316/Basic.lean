module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSeqEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.natShiftEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterProdIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.projN
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.eq_of_fiber_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_ne
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.subset_single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.interUpTo_subset_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.reconstruct_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.le_of_component_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}


theorem subset_of_fiber_subset {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i ⊆ fiber W' i) :
    W ⊆ W' := fun ⟨i, _⟩ ha => h i ha

variable (V : NeighborhoodSystem α)


variable {V}


open ApproximableMap


@[simp] theorem projN_rel {n : ℕ} {W : Set (ℕ × α)} {X : Set α} :
    (projN V n).rel W X ↔ (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X := Iff.rfl

@[simp] theorem toElementMap_projN (z : (iterSys V).Element) (n : ℕ) :
    (projN V n).toElementMap z = component z n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨W, hzW, hW, hX, hsub⟩
    refine ⟨hX, z.up_mem hzW (single_mem hX) ?_⟩
    refine subset_of_fiber_subset (fun i => ?_)
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hsub
    · rw [fiber_single_ne h]; exact V.sub_master (hW.1 i)
  · rintro ⟨hX, hz⟩
    exact ⟨single V n X, hz, single_mem hX, hX, by rw [fiber_single_self]⟩
end DomainTheory.NeighbourhoodSystems
