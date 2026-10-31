module

public import Mathlib.Order.BourbakiWitt
import DomainTheory.ContinuousLattice.ScottMaps.preservesDirectedSup_monotone
import DomainTheory.ContinuousLattice.ScottMaps.scottOpen_preimage
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.ScottMaps.proposition_2_5 -- shake: keep

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

def ScottMap (D : Type u) (D' : Type v) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }

namespace ScottMap

instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1

@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

def const (c : D') : ScottMap D D' :=
  ⟨fun _ => c, PreservesDirectedSup.continuous_of fun S hS _ => by
    obtain ⟨x, hx⟩ := hS
    apply le_antisymm
    · exact le_sSup ⟨x, hx, rfl⟩
    · apply sSup_le
      intro b hb
      obtain ⟨y, hy, rfl⟩ := hb
      exact le_rfl⟩

@[simp] theorem const_apply (c : D') (x : D) : (ScottMap.const c : D → D') x = c := rfl

def le {D : Type u} {D' : Type v} [CompleteLattice D] [CompleteLattice D']
    (f g : ScottMap D D') : Prop :=
  letI : LE D' :=
    (ChainCompletePartialOrder.instOfCompleteLattice
      (α := D')).toPartialOrder.toPreorder.toLE
  ∀ x, f x ≤ g x

def lt {D : Type u} {D' : Type v} [CompleteLattice D] [CompleteLattice D']
    (f g : ScottMap D D') : Prop :=
  ScottMap.le f g ∧ ¬ ScottMap.le g f

theorem le_refl' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f : ScottMap D D') :
    ScottMap.le f f :=
  fun _ => le_rfl

theorem le_trans' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g h : ScottMap D D')
    (hfg : ScottMap.le f g) (hgh : ScottMap.le g h) : ScottMap.le f h :=
  fun x => le_trans (hfg x) (hgh x)

theorem le_antisymm' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D')
    (hfg : ScottMap.le f g) (hgf : ScottMap.le g f) : f = g :=
  ScottMap.ext fun x => le_antisymm (hfg x) (hgf x)

theorem lt_iff_le_not_ge' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D') :
    ScottMap.lt f g ↔ ScottMap.le f g ∧ ¬ ScottMap.le g f :=
  Iff.rfl

instance instPartialOrder {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : PartialOrder (ScottMap D D') where
  le := ScottMap.le
  lt := ScottMap.lt
  le_refl := le_refl'
  le_trans := le_trans'
  lt_iff_le_not_ge := lt_iff_le_not_ge'
  le_antisymm := le_antisymm'

theorem le_def {f g : ScottMap D D'} : f ≤ g ↔ ∀ x, (f : D → D') x ≤ g x := Iff.rfl

theorem preservesDirectedSup_coe (f : ScottMap D D') (S : Set D) (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) :
    (f : D → D') (sSup S) = sSup (Set.image (f : D → D') S) := by
  have h := (proposition_2_5 (Subtype.val f)).mp f.property
  exact h hS hSdir

theorem monotone (f : ScottMap D D') : Monotone (f : D → D') :=
  preservesDirectedSup_monotone ((proposition_2_5 (Subtype.val f)).mp f.property)

theorem pointwise_sSup_preservesDirectedSup (F : Set (ScottMap D D')) :
    PreservesDirectedSup (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) := by
  intro S hS hSdir
  set H := fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)
  show H (sSup S) = sSup (Set.image H S)
  apply le_antisymm
  · apply sSup_le
    intro b hb
    obtain ⟨f, hfF, rfl⟩ := hb
    change f (sSup S) ≤ sSup (Set.image H S)
    rw [f.preservesDirectedSup_coe S hS hSdir]
    apply sSup_le
    intro c hc
    obtain ⟨s, hsS, rfl⟩ := hc
    exact le_trans (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') s) hfF))
      (le_sSup (Set.mem_image_of_mem H hsS))
  · apply sSup_le
    intro b hb
    obtain ⟨s, hsS, rfl⟩ := hb
    apply sSup_le
    intro c hc
    obtain ⟨f, hfF, rfl⟩ := hc
    exact le_trans (ScottMap.monotone f (le_sSup hsS))
      (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') (sSup S)) hfF))

theorem sSupMaps_continuous {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace
      (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) :=
  PreservesDirectedSup.continuous_of (pointwise_sSup_preservesDirectedSup F)

noncomputable def sSupMaps {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) : ScottMap D D' :=
  ⟨fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F),
    sSupMaps_continuous F⟩

theorem sSupMaps_apply (F : Set (ScottMap D D')) (x : D) :
    (sSupMaps F : D → D') x =
      sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F) :=
  rfl

noncomputable instance instSupSet {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : SupSet (ScottMap D D') := ⟨sSupMaps⟩

theorem sSup_apply (F : Set (ScottMap D D')) (x : D) :
    ((sSup F : ScottMap D D') : D → D') x =
      sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F) :=
  rfl

theorem isLUB_sSup {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) :
    IsLUB F (sSup F) := by
  constructor
  · intro f hf
    rw [le_def]
    intro x
    rw [sSup_apply]
    exact le_sSup (Set.mem_image_of_mem _ hf)
  · intro g hg
    rw [le_def]
    intro x
    rw [sSup_apply]
    refine sSup_le ?_
    rintro _ ⟨f, hfF, rfl⟩
    exact (hg hfF) x

noncomputable instance instCompleteLattice {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : CompleteLattice (ScottMap D D') :=
  completeLatticeOfSup (ScottMap D D') isLUB_sSup

theorem preservesDirectedSup_comp {f : D' → D''} {g : D → D'} (hf : PreservesDirectedSup f)
    (hg : PreservesDirectedSup g) : PreservesDirectedSup (f ∘ g) := by
  intro S hS hSdir
  have hmono : Monotone g := preservesDirectedSup_monotone hg
  have hdir' : DirectedOn (· ≤ ·) (g '' S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨g c, Set.mem_image_of_mem g hc, hmono hac, hmono hbc⟩
  have hne : (g '' S).Nonempty := Set.image_nonempty.2 hS
  rw [Function.comp_apply, hg hS hSdir, hf hne hdir']
  congr 1
  exact (Set.image_comp f g S).symm

def comp (f : ScottMap D' D'') (g : ScottMap D D') : ScottMap D D'' :=
  ⟨f ∘ g, PreservesDirectedSup.continuous_of (preservesDirectedSup_comp
    ((proposition_2_5 (Subtype.val f)).mp f.property)
    ((proposition_2_5 (Subtype.val g)).mp g.property))⟩

@[simp] theorem comp_apply (f : ScottMap D' D'') (g : ScottMap D D') (x : D) :
    (f.comp g : D → D'') x = f (g x) := rfl

theorem continuous (f : ScottMap D D') :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f :=
  f.2

def idMap : ScottMap D D :=
  ⟨fun x => x, PreservesDirectedSup.continuous_of fun S _ _ => by
    show sSup S = sSup (Set.image (fun x => x) S)
    rw [Set.image_id']⟩

@[simp] theorem idMap_apply (x : D) : (idMap : ScottMap D D) x = x := rfl

/-- Scott projection on `[D → D]`: `j.comp j = j` and `j ≤ idMap`. -/
def IsProjection (j : ScottMap D D) : Prop :=
  j.comp j = j ∧ j ≤ idMap

theorem bot_apply (x : D) : ((⊥ : ScottMap D D') : D → D') x = ⊥ := by
  have h : (⊥ : ScottMap D D') = sSup (∅ : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_empty, sSup_empty]

theorem sup_apply (f g : ScottMap D D') (x : D) :
    ((f ⊔ g : ScottMap D D') : D → D') x = f x ⊔ g x := by
  have h : (f ⊔ g : ScottMap D D') = sSup ({f, g} : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_pair]
  exact sSup_pair

theorem sInf_image_le_of_mem {f' : ScottMap D D'} {U : Set D} {y : D} (hyU : y ∈ U) :
    sInf (Set.image (f' : D → D') U) ≤ f' y :=
  sInf_le (Set.mem_image_of_mem _ hyU)

theorem eq_sSup_openInfs (hD' : ContinuousLattice D') (f' : ScottMap D D') (y : D) :
    (f' : D → D') y =
      sSup { d | ∃ U, @IsOpen D scottTopologicalSpace U ∧ y ∈ U ∧
        d = sInf (Set.image (f' : D → D') U) } := by
  apply le_antisymm
  · rw [← hD'.sSup_wayBelow (f' y)]
    apply sSup_le
    intro a ha
    obtain ⟨V, hV, hf'V, hVsub⟩ := ha
    have hyU : y ∈ (f' : D → D') ⁻¹' V := hf'V
    have hUScott : ScottOpen ((f' : D → D') ⁻¹' V) :=
      scottOpen_preimage ((proposition_2_5 (Subtype.val f')).mp f'.property) hV
    have hUopen : @IsOpen D scottTopologicalSpace ((f' : D → D') ⁻¹' V) :=
      ScottOpen.isOpen_iff.mpr hUScott
    have ha' : a ≤ sInf (Set.image (f' : D → D') ((f' : D → D') ⁻¹' V)) := by
      apply le_sInf
      intro d hd
      obtain ⟨z, hzV, rfl⟩ := hd
      exact Set.mem_Ici.1 (hVsub hzV)
    have hmem : sInf (Set.image (f' : D → D') ((f' : D → D') ⁻¹' V)) ∈
        { d | ∃ U, @IsOpen D scottTopologicalSpace U ∧ y ∈ U ∧
          d = sInf (Set.image (f' : D → D') U) } :=
      ⟨(f' : D → D') ⁻¹' V, hUopen, hyU, rfl⟩
    exact le_trans ha' (le_sSup hmem)
  · apply sSup_le
    intro d hd
    obtain ⟨U, _hUopen, hyU, rfl⟩ := hd
    exact sInf_image_le_of_mem (f' := f') (y := y) (U := U) hyU

end ScottMap

end DomainTheory.ContinuousLattice
