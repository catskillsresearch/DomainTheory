module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.projectionPair
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

def Trianglelefteq (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq

section ProjectionPairFromMaps

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

def IsGen (X : Set α) (Y : Set β) : Prop := i.rel X Y ∧ j.rel Y X

theorem isGen_exists (hji : j.comp i = idMap D) {X : Set α} (hX : D.mem X) :
    ∃ Y, IsGen i j X Y := by
  have hrel : (j.comp i).rel X X := by rw [hji]; exact ⟨hX, hX, subset_rfl⟩
  obtain ⟨Y, hiXY, hjYX⟩ := hrel
  exact ⟨Y, hiXY, hjYX⟩

theorem isGen_inter {X X' : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y') (hE : E.mem (Y ∩ Y')) :
    IsGen i j (X ∩ X') (Y ∩ Y') := by
  obtain ⟨hiXY, hjYX⟩ := h
  obtain ⟨hiX'Y', hjY'X'⟩ := h'
  have hj1 : j.rel (Y ∩ Y') X :=
    j.mono hjYX Set.inter_subset_left subset_rfl hE (j.rel_cod hjYX)
  have hj2 : j.rel (Y ∩ Y') X' :=
    j.mono hjY'X' Set.inter_subset_right subset_rfl hE (j.rel_cod hjY'X')
  have hjInter : j.rel (Y ∩ Y') (X ∩ X') := j.inter_right hj1 hj2
  have hDXX' : D.mem (X ∩ X') := j.rel_cod hjInter
  have hi1 : i.rel (X ∩ X') Y :=
    i.mono hiXY Set.inter_subset_left subset_rfl hDXX' (i.rel_cod hiXY)
  have hi2 : i.rel (X ∩ X') Y' :=
    i.mono hiX'Y' Set.inter_subset_right subset_rfl hDXX' (i.rel_cod hiX'Y')
  exact ⟨i.inter_right hi1 hi2, hjInter⟩

theorem isGen_master : IsGen i j D.master E.master :=
  ⟨i.master_rel, j.master_rel⟩

def Dprime : NeighborhoodSystem β where
  mem Y := ∃ X, IsGen i j X Y
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := ⟨D.master, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ Z ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ ⟨_, hgz⟩ hZsub
    have hEY₁ : E.mem Y₁ := i.rel_cod hg₁.1
    have hEY₂ : E.mem Y₂ := i.rel_cod hg₂.1
    have hEZ : E.mem Z := i.rel_cod hgz.1
    have hEinter : E.mem (Y₁ ∩ Y₂) := E.inter_mem hEY₁ hEY₂ hEZ hZsub
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hEinter⟩
  sub_master := by
    rintro Y ⟨X, hg⟩
    exact E.sub_master (i.rel_cod hg.1)

theorem isGen_mono (hji : j.comp i = idMap D) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hZW : Z ⊆ W) : X ⊆ X' := by
  obtain ⟨hiXZ, _⟩ := h
  obtain ⟨_, hjWX'⟩ := h'
  have hiXW : i.rel X W :=
    i.mono hiXZ subset_rfl hZW (i.rel_dom hiXZ) (j.rel_dom hjWX')
  have hrel : (j.comp i).rel X X' := ⟨W, hiXW, hjWX'⟩
  rw [hji] at hrel
  exact hrel.2.2

theorem isGen_fst_unique (hji : j.comp i = idMap D) {X X' : Set α} {Y : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y) : X = X' :=
  Set.Subset.antisymm (isGen_mono i j hji h h' subset_rfl)
    (isGen_mono i j hji h' h subset_rfl)

theorem isGen_mono' (hij : i.comp j ≤ idMap E) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hXX' : X ⊆ X') : Z ⊆ W := by
  obtain ⟨_, hjZX⟩ := h
  obtain ⟨hiX'W, _⟩ := h'
  have hjZX' : j.rel Z X' :=
    j.mono hjZX subset_rfl hXX' (j.rel_dom hjZX) (i.rel_dom hiX'W)
  have hrel : (i.comp j).rel Z W := ⟨X', hjZX', hiX'W⟩
  exact (hij Z W hrel).2.2

theorem isGen_snd_unique (hij : i.comp j ≤ idMap E) {X : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X Y') : Y = Y' :=
  Set.Subset.antisymm (isGen_mono' i j hij h h' subset_rfl)
    (isGen_mono' i j hij h' h subset_rfl)

@[simp] theorem mem_Dprime {Y : Set β} : (Dprime i j).mem Y ↔ ∃ X, IsGen i j X Y := Iff.rfl

theorem Dprime_subsystem : Dprime i j ◁ E where
  master_eq := rfl
  sub := by rintro Y ⟨X, hg⟩; exact i.rel_cod hg.1
  inter_closed := by
    rintro Y₁ Y₂ ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ hE
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hE⟩

def ofEl (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E)
    (y : (Dprime i j).Element) : D.Element where
  mem X := ∃ Y, y.mem Y ∧ IsGen i j X Y
  sub := by rintro X ⟨Y, _, hg⟩; exact i.rel_dom hg.1
  master_mem := ⟨E.master, y.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁y, hg₁⟩ ⟨Y₂, hY₂y, hg₂⟩
    have hyInter : y.mem (Y₁ ∩ Y₂) := y.inter_mem hY₁y hY₂y
    have hEInter : E.mem (Y₁ ∩ Y₂) := (Dprime_subsystem i j).sub (y.sub hyInter)
    exact ⟨Y₁ ∩ Y₂, hyInter, isGen_inter i j hg₁ hg₂ hEInter⟩
  up_mem := by
    rintro X X' ⟨Y, hYy, hg⟩ hDX' hXX'
    obtain ⟨Y', hg'⟩ := isGen_exists i j hji hDX'
    have hYY' : Y ⊆ Y' := isGen_mono' i j hij hg hg' hXX'
    exact ⟨Y', y.up_mem hYy ⟨X', hg'⟩ hYY', hg'⟩

def toEl (hji : j.comp i = idMap D) (x : D.Element) : (Dprime i j).Element where
  mem Y := ∃ X, x.mem X ∧ IsGen i j X Y
  sub := by rintro Y ⟨X, _, hg⟩; exact ⟨X, hg⟩
  master_mem := ⟨D.master, x.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ ⟨X₁, hX₁x, hg₁⟩ ⟨X₂, hX₂x, hg₂⟩
    have hxInter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁x hX₂x
    have hDInter : D.mem (X₁ ∩ X₂) := x.sub hxInter
    have hi1 : i.rel (X₁ ∩ X₂) Y₁ :=
      i.mono hg₁.1 Set.inter_subset_left subset_rfl hDInter (i.rel_cod hg₁.1)
    have hi2 : i.rel (X₁ ∩ X₂) Y₂ :=
      i.mono hg₂.1 Set.inter_subset_right subset_rfl hDInter (i.rel_cod hg₂.1)
    have hEinter : E.mem (Y₁ ∩ Y₂) := i.rel_cod (i.inter_right hi1 hi2)
    exact ⟨X₁ ∩ X₂, hxInter, isGen_inter i j hg₁ hg₂ hEinter⟩
  up_mem := by
    rintro Y Y' ⟨X, hXx, hg⟩ ⟨X', hg'⟩ hYY'
    have hXX' : X ⊆ X' := isGen_mono i j hji hg hg' hYY'
    exact ⟨X', x.up_mem hXx (i.rel_dom hg'.1) hXX', hg'⟩

def dprimeEquiv (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
    D.Element ≃o (Dprime i j).Element where
  toFun := toEl i j hji
  invFun := ofEl i j hji hij
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨Y, ⟨X₁, hX₁x, hg₁⟩, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x
    · intro hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      exact ⟨Y, ⟨X, hXx, hg⟩, hg⟩
  right_inv := by
    intro y
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨X, ⟨Y₁, hY₁y, hg₁⟩, hg⟩
      rw [isGen_snd_unique i j hij hg hg₁]; exact hY₁y
    · intro hYy
      obtain ⟨X, hg⟩ := y.sub hYy
      exact ⟨X, ⟨Y, hYy, hg⟩, hg⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      obtain ⟨X₁, hX₁x', hg₁⟩ := h Y ⟨X, hXx, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x'
    · rintro h Y ⟨X, hXx, hg⟩
      exact ⟨X, h X hXx, hg⟩

end ProjectionPairFromMaps

theorem trianglelefteq_of_projectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

namespace Subsystem.ProjectionPair

variable {α : Type*} {D E : NeighborhoodSystem α}

def lowerSet (P : ProjectionPair D E) (y : E.Element) : Set D.Element :=
  {x | P.inj.toElementMap x ≤ y}

@[simp] theorem mem_lowerSet (P : ProjectionPair D E) {y : E.Element} {x : D.Element} :
    x ∈ P.lowerSet y ↔ P.inj.toElementMap x ≤ y := Iff.rfl

def upperSet (P : ProjectionPair D E) (x : D.Element) : Set E.Element :=
  {y | x ≤ P.proj.toElementMap y}

@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

end Subsystem.ProjectionPair

end DomainTheory.NeighbourhoodSystems
