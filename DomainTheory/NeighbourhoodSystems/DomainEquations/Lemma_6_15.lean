module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
section ProjectionPair
variable (i : ApproximableMap D E) (j : ApproximableMap E D)

theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair
end

section
set_option linter.unusedVariables false

theorem theorem_615.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (i : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β D E)
  (j : @DomainTheory.NeighbourhoodSystems.ApproximableMap β α E D),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β α D E D j i)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D) →
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap β β E E)
            (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap β β E E)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp β α β E D E i j)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap β E) →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E :=
  @DomainTheory.NeighbourhoodSystems.trianglelefteq_of_projectionPair
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems
namespace Subsystem
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}
variable {D E : NeighborhoodSystem α}

structure ProjectionPair (D E : NeighborhoodSystem α) where

  inj : ApproximableMap D E

  proj : ApproximableMap E D

  proj_comp_inj : proj.comp inj = idMap D

  inj_comp_proj_le : inj.comp proj ≤ idMap E
end

end Subsystem
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

def inj (h : D ◁ E) : ApproximableMap D E where
  rel X Y := D.mem X ∧ E.mem Y ∧ X ⊆ Y
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨D.master_mem, E.master_mem, h.master_eq.subset⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, E.inter_mem hY hY' (h.sub hX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

@[simp] theorem inj_rel (h : D ◁ E) {X Y : Set α} :
    (h.inj).rel X Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y := Iff.rfl

def proj (h : D ◁ E) : ApproximableMap E D where
  rel Y X := E.mem Y ∧ D.mem X ∧ Y ⊆ X
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨E.master_mem, D.master_mem, h.master_eq.symm.subset⟩
  inter_right := by
    rintro Y X X' ⟨hY, hX, hYX⟩ ⟨_, hX', hYX'⟩
    have hEinter : E.mem (X ∩ X') :=
      E.inter_mem (h.sub hX) (h.sub hX') hY (Set.subset_inter hYX hYX')
    exact ⟨hY, h.inter_closed hX hX' hEinter, Set.subset_inter hYX hYX'⟩
  mono := by
    rintro Y Y' X X' ⟨_, _, hYX⟩ hY'Y hXX' hY' hX'
    exact ⟨hY', hX', (hY'Y.trans hYX).trans hXX'⟩

@[simp] theorem proj_rel (h : D ◁ E) {Y X : Set α} :
    (h.proj).rel Y X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X := Iff.rfl

theorem inj_comp_proj_le (h : D ◁ E) : h.inj.comp h.proj ≤ idMap E := by
  intro Y Y' hr
  obtain ⟨X, ⟨hEY, _, hYX⟩, _, hEY', hXY'⟩ := hr
  exact ⟨hEY, hEY', hYX.trans hXY'⟩

theorem proj_comp_inj (h : D ◁ E) : h.proj.comp h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, _, hZ, hYZ⟩
    exact ⟨hX, hZ, hXY.trans hYZ⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨Z, ⟨hX, h.sub hZ, hXZ⟩, h.sub hZ, hZ, subset_rfl⟩

end Subsystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem
section
set_option linter.unusedVariables false

theorem theorem_612.{u_1} : And
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D)) :=
  @And.intro
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E D E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α D E D
        (@DomainTheory.NeighbourhoodSystems.Subsystem.proj α D E h)
        (@DomainTheory.NeighbourhoodSystems.Subsystem.inj α D E h))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α D))
  @DomainTheory.NeighbourhoodSystems.Subsystem.inj_comp_proj_le
  @DomainTheory.NeighbourhoodSystems.Subsystem.proj_comp_inj
end

end DomainTheory.NeighbourhoodSystems.Subsystem
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Subsystem

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

def lowerSet (P : ProjectionPair D E) (y : E.Element) : Set D.Element :=
  {x | P.inj.toElementMap x ≤ y}

@[simp] theorem mem_lowerSet (P : ProjectionPair D E) {y : E.Element} {x : D.Element} :
    x ∈ P.lowerSet y ↔ P.inj.toElementMap x ≤ y := Iff.rfl

def upperSet (P : ProjectionPair D E) (x : D.Element) : Set E.Element :=
  {y | x ≤ P.proj.toElementMap y}

@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

end Subsystem.ProjectionPair
end
end DomainTheory.NeighbourhoodSystems
end
