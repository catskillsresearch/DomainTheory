module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Specialization.SpecializationPreorder
public import DomainTheory.ContinuousLattice.FunctionSpaces.continuousMapInducedPiTopology
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5
public import DomainTheory.ContinuousLattice.ScottMaps.scottOpen_preimage
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

section Def3_1

variable [TopologicalSpace X] [TopologicalSpace Y]

def scottFunctionEvalSubbasis (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Set (Set (C(X, Y))) :=
  { W | ∃ (x : X) (U : Set Y), IsOpen U ∧ W = {f : C(X, Y) | f x ∈ U} }

@[reducible] noncomputable def scottFunctionTopology (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (C(X, Y)) :=
  generateFrom (scottFunctionEvalSubbasis X Y)

theorem scottFunctionSubbasis_isOpen {x : X} {U : Set Y} (hU : IsOpen U) :
    @IsOpen (C(X, Y)) (scottFunctionTopology X Y) {f : C(X, Y) | f x ∈ U} :=
  isOpen_generateFrom_of_mem (s := {f : C(X, Y) | f x ∈ U}) ⟨x, U, hU, rfl⟩

theorem scottFunctionTopology_eq_induced_pi (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] :
    scottFunctionTopology X Y = continuousMapInducedPiTopology X Y := by
  apply le_antisymm
  · let : TopologicalSpace C(X, Y) := scottFunctionTopology X Y
    change scottFunctionTopology X Y ≤ continuousMapInducedPiTopology X Y
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU =>
        scottFunctionSubbasis_isOpen (X := X) (Y := Y) (x := x) hU
  · apply le_generateFrom_iff_subset_isOpen.2
    rintro W ⟨x, U, hU, rfl⟩
    change @IsOpen C(X, Y)
      (TopologicalSpace.induced (fun f : C(X, Y) => (f : X → Y))
        (@Pi.topologicalSpace X (fun _ => Y) (fun _ => inferInstance)))
      {f : C(X, Y) | f x ∈ U}
    rw [isOpen_induced_iff]
    exact ⟨{g : X → Y | g x ∈ U}, (@continuous_apply X (fun _ => Y)
      (fun _ => inferInstance) x).isOpen_preimage U hU, rfl⟩

theorem specializationPreorder_generateOpen (f g : C(X, Y)) (hfg : ∀ x, SpecializationPreorder (f x) (g x))
    {V : Set (C(X, Y))} (hV : GenerateOpen (scottFunctionEvalSubbasis X Y) V) (hf : f ∈ V) :
    g ∈ V :=
  match hV with
  | .basic W hW => by
    obtain ⟨x, U, hU, rfl⟩ := hW
    exact hfg x U hU hf
  | .univ => hf
  | .inter s t hs ht => by
    rcases hf with ⟨hfs, hft⟩
    exact Set.mem_inter (specializationPreorder_generateOpen f g hfg hs hfs)
      (specializationPreorder_generateOpen f g hfg ht hft)
  | .sUnion S hS => by
    obtain ⟨W, hWS, hfW⟩ := Set.mem_sUnion.mp hf
    exact Set.mem_sUnion.mpr ⟨W, hWS, specializationPreorder_generateOpen f g hfg (hS W hWS) hfW⟩

theorem scottFunctionSpecializationPreorder {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    SpecializationPreorder f g ↔ ∀ x, SpecializationPreorder (f x) (g x) := by
  let : TopologicalSpace (C(X, Y)) := scottFunctionTopology X Y
  constructor
  · intro hfg x U hU hfU
    exact hfg {h | h x ∈ U} (scottFunctionSubbasis_isOpen (X := X) (Y := Y) hU) hfU
  · intro hfg U hU hfU
    exact specializationPreorder_generateOpen f g hfg hU hfU

variable [CompleteLattice D] [CompleteLattice D']

theorem scottFunctionSubbasis_isOpen_scott {x : D} {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    letI : TopologicalSpace D := scottTopologicalSpace
    letI : TopologicalSpace D' := scottTopologicalSpace
    @IsOpen (C(D, D')) (scottFunctionTopology D D') {f : C(D, D') | f x ∈ U} := by
  let : TopologicalSpace D := scottTopologicalSpace
  let : TopologicalSpace D' := scottTopologicalSpace
  exact isOpen_generateFrom_of_mem (s := {f : C(D, D') | f x ∈ U}) ⟨x, U, hU, rfl⟩

end Def3_1

section ScottMap

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

def ScottMap (D : Type u) (D' : Type v) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

def const (c : D') : ScottMap D D' :=
  ⟨fun _ => c, continuous_of_preservesDirectedSup fun S hS _ => by
    obtain ⟨x, hx⟩ := hS
    apply le_antisymm
    · exact le_sSup ⟨x, hx, rfl⟩
    · apply sSup_le
      intro b hb
      obtain ⟨y, hy, rfl⟩ := hb
      exact le_rfl⟩

@[simp] theorem const_apply (c : D') (x : D) : (ScottMap.const c : D → D') x = c := rfl

end ScottMap

@[reducible] noncomputable def scottMapInducedPiTopology (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
    (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace))

def scottMapPointwiseSubbasis (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :
    Set (Set (ScottMap D D')) :=
  { W | ∃ (x : D) (U : Set D'),
      @IsOpen D' scottTopologicalSpace U ∧ W = {f : ScottMap D D' | (f : D → D') x ∈ U} }

@[reducible] noncomputable def scottMapPointwiseTopology (D D' : Type*)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  generateFrom (scottMapPointwiseSubbasis D D')

theorem pointwiseSubbasic_isOpen (x : D) {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottMap D D') (scottMapPointwiseTopology D D')
      {f : ScottMap D D' | (f : D → D') x ∈ U} :=
  isOpen_generateFrom_of_mem ⟨x, U, hU, rfl⟩

theorem scottMapPointwiseTopology_eq_induced_pi :
    scottMapPointwiseTopology D D' = scottMapInducedPiTopology D D' := by
  apply le_antisymm
  · let : TopologicalSpace D' := scottTopologicalSpace
    let : TopologicalSpace (ScottMap D D') := scottMapPointwiseTopology D D'
    change scottMapPointwiseTopology D D' ≤ scottMapInducedPiTopology D D'
    rw [← continuous_iff_le_induced]
    exact continuous_pi fun x =>
      continuous_def.2 fun U hU => pointwiseSubbasic_isOpen (D := D) (D' := D') x hU
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

end ScottMap

section SubspaceExtension

variable {Y : Type*} [CompleteLattice Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem scottSubspaceExtendInf_le_of_mem {f' : ScottMap Y D} {U : Set Y} {y : Y}
    (hyU : y ∈ U) : sInf (Set.image (f' : Y → D) U) ≤ f' y :=
  sInf_le (Set.mem_image_of_mem _ hyU)

theorem scottMap_eq_sSup_openInfs (hD : ContinuousLattice D) (f' : ScottMap Y D) (y : Y) :
    (f' : Y → D) y =
      sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧
        d = sInf (Set.image (f' : Y → D) U) } := by
  apply le_antisymm
  · rw [← hD.sSup_wayBelow (f' y)]
    apply sSup_le
    intro a ha
    obtain ⟨V, hV, hf'V, hVsub⟩ := ha
    have hVopen : @IsOpen D scottTopologicalSpace V := ScottOpen.isOpen_iff.mpr hV
    have hyU : y ∈ (f' : Y → D) ⁻¹' V := hf'V
    have hUScott : ScottOpen ((f' : Y → D) ⁻¹' V) :=
      scottOpen_preimage ((proposition_2_5 (Subtype.val f')).mp f'.property) hV
    have hUopen : @IsOpen Y scottTopologicalSpace ((f' : Y → D) ⁻¹' V) :=
      ScottOpen.isOpen_iff.mpr hUScott
    have ha' : a ≤ sInf (Set.image (f' : Y → D) ((f' : Y → D) ⁻¹' V)) := by
      apply le_sInf
      intro d hd
      obtain ⟨z, hzV, rfl⟩ := hd
      exact Set.mem_Ici.1 (hVsub hzV)
    have hmem : sInf (Set.image (f' : Y → D) ((f' : Y → D) ⁻¹' V)) ∈
        { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧
          d = sInf (Set.image (f' : Y → D) U) } :=
      ⟨(f' : Y → D) ⁻¹' V, hUopen, hyU, rfl⟩
    exact le_trans ha' (le_sSup hmem)
  · apply sSup_le
    intro d hd
    obtain ⟨U, _hUopen, hyU, rfl⟩ := hd
    exact scottSubspaceExtendInf_le_of_mem (f' := f') (y := y) (U := U) hyU

end SubspaceExtension

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

end DomainTheory.ContinuousLattice
