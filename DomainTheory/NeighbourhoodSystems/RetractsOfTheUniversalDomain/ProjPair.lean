module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_6

@[expose] public section

section
universe u v w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type u} {β : Type v} {γ : Type w}

structure ProjPair (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) where

  inj : ApproximableMap D E

  proj : ApproximableMap E D

  proj_comp_inj : proj.comp inj = idMap D

  inj_comp_proj_le : inj.comp proj ≤ idMap E

namespace ProjPair

def comp {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (p1 : ProjPair D E) (p2 : ProjPair E F) :
    ProjPair D F where
  inj := p2.inj.comp p1.inj
  proj := p1.proj.comp p2.proj
  proj_comp_inj := by
    show (p1.proj.comp p2.proj).comp (p2.inj.comp p1.inj) = idMap D
    rw [comp_assoc, ← comp_assoc p2.proj p2.inj p1.inj, p2.proj_comp_inj, idMap_comp,
      p1.proj_comp_inj]
  inj_comp_proj_le := by
    show (p2.inj.comp p1.inj).comp (p1.proj.comp p2.proj) ≤ idMap F
    rw [comp_assoc, ← comp_assoc p1.inj p1.proj p2.proj]
    calc p2.inj.comp ((p1.inj.comp p1.proj).comp p2.proj)
        ≤ p2.inj.comp ((idMap E).comp p2.proj) :=
          comp_mono_gen le_rfl (comp_mono_gen p1.inj_comp_proj_le le_rfl)
      _ = p2.inj.comp p2.proj := by rw [idMap_comp]
      _ ≤ idMap F := p2.inj_comp_proj_le

def ofIso {D : NeighborhoodSystem α} {E : NeighborhoodSystem β} (e : DomainIso D E) :
    ProjPair D E where
  inj := ApproximableMap.ofIso e
  proj := ApproximableMap.ofIso e.symm
  proj_comp_inj := by
    have heq : ∀ x, ((ApproximableMap.ofIso e.symm).comp (ApproximableMap.ofIso e)).toElementMap x
        = (idMap D).toElementMap x := by
      intro x
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
        toElementMap_idMap]
    exact le_antisymm (le_iff_toElementMap_le.mpr fun x => (heq x).le)
      (le_iff_toElementMap_le.mpr fun x => (heq x).ge)
  inj_comp_proj_le := by
    have heq : ∀ y, ((ApproximableMap.ofIso e).comp (ApproximableMap.ofIso e.symm)).toElementMap y
        = (idMap E).toElementMap y := by
      intro y
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
        toElementMap_idMap]
    exact le_iff_toElementMap_le.mpr fun y => (heq y).le

def ofSubsystem {D E : NeighborhoodSystem α} (h : D ◁ E) : ProjPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end ProjPair

end DomainTheory.NeighbourhoodSystems
end
