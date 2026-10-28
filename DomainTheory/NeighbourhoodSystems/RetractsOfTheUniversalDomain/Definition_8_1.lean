module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma_6_15

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α : Type*} {E : NeighborhoodSystem α}

class Retraction (a : ApproximableMap E E) : Prop where
  out : a.comp a = a

@[simp] theorem isRetraction_idMap : Retraction (idMap E) :=
  ⟨idMap_comp (idMap E)⟩

end

section
open NeighborhoodSystem ApproximableMap
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem

def retractionOfSubsystem (h : D ◁ E) : ApproximableMap E E := h.inj.comp h.proj

@[simp] theorem retractionOfSubsystem_rel (h : D ◁ E) {X Z : Set α} :
    (retractionOfSubsystem h).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, D.mem Y ∧ X ⊆ Y ∧ Y ⊆ Z := by
  simp only [retractionOfSubsystem, comp_rel, inj_rel, proj_rel]
  constructor
  · rintro ⟨Y, ⟨hEX, hDY, hXY⟩, hDY', hEZ, hYZ⟩
    exact ⟨hEX, hEZ, Y, hDY, hXY, hYZ⟩
  · rintro ⟨hEX, hEZ, Y, hDY, hXY, hYZ⟩
    exact ⟨Y, ⟨hEX, hDY, hXY⟩, hDY, hEZ, hYZ⟩

theorem retractionOfSubsystem_toElementMap_inj (h : D ◁ E) (x : D.Element) :
    (retractionOfSubsystem h).toElementMap (h.inj.toElementMap x) = h.inj.toElementMap x := by
  have h1 : (retractionOfSubsystem h).toElementMap (h.inj.toElementMap x)
      = h.inj.toElementMap (h.proj.toElementMap (h.inj.toElementMap x)) :=
    toElementMap_comp h.inj h.proj (h.inj.toElementMap x)
  have h2 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
    (toElementMap_comp h.proj h.inj x).symm
  rw [h1, h2, h.proj_comp_inj, toElementMap_idMap]

def elementIso (h : D ◁ E) :
    D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y} where
  toFun x := ⟨h.inj.toElementMap x, retractionOfSubsystem_toElementMap_inj h x⟩
  invFun y := h.proj.toElementMap y.1
  left_inv x := by
    have h1 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
      (toElementMap_comp h.proj h.inj x).symm
    show h.proj.toElementMap (h.inj.toElementMap x) = x
    rw [h1, h.proj_comp_inj, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : (h.inj.comp h.proj).toElementMap y.1 = y.1 := y.2
    have h1 : (h.inj.comp h.proj).toElementMap y.1 = h.inj.toElementMap (h.proj.toElementMap y.1) :=
      toElementMap_comp h.inj h.proj y.1
    show h.inj.toElementMap (h.proj.toElementMap y.1) = y.1
    rw [← h1]; exact hfix
  map_rel_iff' := by
    intro x x'
    show h.inj.toElementMap x ≤ h.inj.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := h.proj.toElementMap_mono hle
      have h1 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
        (toElementMap_comp h.proj h.inj x).symm
      have h2 : h.proj.toElementMap (h.inj.toElementMap x') = (h.proj.comp h.inj).toElementMap x' :=
        (toElementMap_comp h.proj h.inj x').symm
      rw [h1, h2, h.proj_comp_inj, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact h.inj.toElementMap_mono hle

theorem isRetraction_retractionOfSubsystem (h : D ◁ E) :
    Retraction (retractionOfSubsystem h) := by
  constructor
  show (h.inj.comp h.proj).comp (h.inj.comp h.proj) = h.inj.comp h.proj
  rw [comp_assoc, ← comp_assoc h.proj h.inj h.proj, h.proj_comp_inj, idMap_comp]

end Subsystem
end
end DomainTheory.NeighbourhoodSystems
