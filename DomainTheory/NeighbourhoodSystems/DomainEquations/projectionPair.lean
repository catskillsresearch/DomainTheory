module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.subdomain
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.step

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

structure ProjectionPair (D E : NeighborhoodSystem α) where
  inj : ApproximableMap D E
  proj : ApproximableMap E D
  proj_comp_inj : proj.comp inj = idMap D
  inj_comp_proj_le : inj.comp proj ≤ idMap E

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

def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end Subsystem

end DomainTheory.NeighbourhoodSystems
