module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_scottOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_le_finset_sup_step
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_finset_sup

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

@[reducible] noncomputable def scottMapInducedPiTopology (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
    (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace))

namespace scottMapInducedPiTopology

section

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

def pointwiseSubbasis (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :
    Set (Set (ScottMap D D')) :=
  { W | ∃ (x : D) (U : Set D'),
      @IsOpen D' scottTopologicalSpace U ∧ W = {f : ScottMap D D' | (f : D → D') x ∈ U} }

@[reducible] noncomputable def pointwiseTopology (D D' : Type*)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  generateFrom (pointwiseSubbasis D D')

theorem subbasic_isOpen (x : D) {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottMap D D') (pointwiseTopology D D')
      {f : ScottMap D D' | (f : D → D') x ∈ U} :=
  isOpen_generateFrom_of_mem ⟨x, U, hU, rfl⟩

theorem eq_induced_pi :
    pointwiseTopology D D' = scottMapInducedPiTopology D D' := by
  apply le_antisymm
  · let : TopologicalSpace D' := scottTopologicalSpace
    let : TopologicalSpace (ScottMap D D') := pointwiseTopology D D'
    change pointwiseTopology D D' ≤ scottMapInducedPiTopology D D'
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU => subbasic_isOpen (D := D) (D' := D') x hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    let : TopologicalSpace D' := scottTopologicalSpace
    change @IsOpen (ScottMap D D')
      (TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
        (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace)))
      {f : ScottMap D D' | (f : D → D') x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : D → D' | g x ∈ U}, (@continuous_apply D (fun _ => D')
      (fun _ => scottTopologicalSpace) x).isOpen_preimage U hU, rfl⟩

theorem scottTopology_eq_pointwise (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      pointwiseTopology D D' := by
  have hL : ContinuousLattice (ScottMap D D') := stepMap.isContinuousLattice hD hD'
  apply le_antisymm
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hUopen, rfl⟩
    exact ScottOpen.isOpen_iff.mpr (pointwiseSubbasic_scottOpen x (ScottOpen.isOpen_iff.mp hUopen))
  · intro U hU
    rw [ScottOpen.isOpen_iff] at hU
    rw [@isOpen_iff_forall_mem_open (ScottMap D D') (pointwiseTopology D D')]
    intro g hgU
    obtain ⟨φ, hφg, hφsub⟩ := exists_wayBelow_subset hL hU hgU
    obtain ⟨F, hF, hφF⟩ := wayBelow_le_finset_sup_step hD hD' hφg
    refine ⟨⋂ p ∈ F, {h : ScottMap D D' | (p.2 : D') ≪ (h : D → D') p.1}, ?_, ?_, ?_⟩
    · intro h hh
      refine hφsub (WayBelow.le_trans hφF (wayBelow_finset_sup fun p hp => ?_))
      exact stepMap.wayBelow (Set.mem_iInter₂.1 hh p hp)
    · exact @isOpen_biInter_finset (ScottMap D D') (D × D') (pointwiseTopology D D') F _
        (fun p _ => subbasic_isOpen p.1 (ScottOpen.isOpen_iff.mpr (ScottOpen.wayBelow p.2)))
    · exact Set.mem_iInter₂.2 fun p hp => hF p hp

theorem scottTopology_eq_inducedPi (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      scottMapInducedPiTopology D D' := by
  rw [scottTopology_eq_pointwise hD hD', eq_induced_pi]

end

end scottMapInducedPiTopology

end DomainTheory.ContinuousLattice
