module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofContinuous
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.eq_principal_of_isMin
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal_le_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.O
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

def memO (X : Set (Fin 1)) : Prop := X = Set.univ ∨ X = ∅

theorem nestedOrDisjoint_O : NestedOrDisjoint memO := by
  rintro X Y (rfl | rfl) (rfl | rfl)
  · exact Or.inl subset_rfl
  · exact Or.inr (Or.inl (Set.empty_subset _))
  · exact Or.inl (Set.empty_subset _)
  · exact Or.inl subset_rfl

theorem subMaster_O : ∀ {X : Set (Fin 1)}, memO X → X ⊆ Set.univ := fun _ => Set.subset_univ _

/-- One-token Sierpiński neighbourhood system: master and empty. -/
def system : NeighborhoodSystem (Fin 1) :=
  NeighborhoodSystem.ofNestedOrDisjoint memO Set.univ Set.univ_nonempty
    (Or.inl rfl) nestedOrDisjoint_O subMaster_O

@[simp] theorem O_mem {X : Set (Fin 1)} : system.mem X ↔ memO X := Iff.rfl

@[simp] theorem O_master : system.master = (Set.univ : Set (Fin 1)) := rfl

theorem O_mem_empty : system.mem (∅ : Set (Fin 1)) := Or.inr rfl

theorem O_inter_mem {Y Y' : Set (Fin 1)} (hY : system.mem Y) (hY' : system.mem Y') : system.mem (Y ∩ Y') := by
  rcases hY with rfl | rfl
  · rw [Set.univ_inter]; exact hY'
  · rw [Set.empty_inter]; exact O_mem_empty

def botElt : system.Element := system.bot

theorem mem_botElt {Y : Set (Fin 1)} : botElt.mem Y ↔ Y = (Set.univ : Set (Fin 1)) := by
  rw [botElt, system.mem_bot, O_master]

def topElt : system.Element := system.principal O_mem_empty

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- Open set classified by an approximable map into the Sierpiński system. -/
def mapToOpen (f : ApproximableMap V system) : Set V.Element := {x | f.toElementMap x = topElt}
end

theorem mem_empty_iff_eq_top (z : system.Element) : z.mem ∅ ↔ z = topElt := by
  constructor
  · intro hz
    exact system.eq_principal_of_isMin z hz (fun Y _ => Set.empty_subset Y)
  · rintro rfl
    exact ⟨O_mem_empty, subset_rfl⟩

theorem element_eq_bot_or_top (z : system.Element) : z = botElt ∨ z = topElt := by
  by_cases hz : z.mem ∅
  · exact Or.inr ((mem_empty_iff_eq_top z).mp hz)
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    constructor
    · intro hY
      rcases (O_mem.mp (z.sub hY)) with rfl | rfl
      · exact mem_botElt.mpr rfl
      · exact absurd hY hz
    · intro hY
      rw [mem_botElt.mp hY, ← O_master]
      exact z.master_mem

theorem O_ext {z w : system.Element} (h : z.mem ∅ ↔ w.mem ∅) : z = w := by
  by_cases hz : z.mem ∅
  · rw [(mem_empty_iff_eq_top z).mp hz, (mem_empty_iff_eq_top w).mp (h.mp hz)]
  · have ez : z = botElt :=
      (element_eq_bot_or_top z).resolve_right (fun c => hz ((mem_empty_iff_eq_top z).mpr c))
    have ew : w = botElt :=
      (element_eq_bot_or_top w).resolve_right
        (fun c => (fun c' => hz (h.mpr c')) ((mem_empty_iff_eq_top w).mpr c))
    rw [ez, ew]

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

theorem isOpen_mapToOpen (f : ApproximableMap V system) : IsOpen (mapToOpen V f) := by
  have heq : mapToOpen V f = (fun x => f.toElementMap x) ⁻¹' system.basicOpen ∅ := by
    ext x
    simp only [mapToOpen, Set.mem_ofPred_eq, Set.mem_preimage, mem_basicOpen]
    exact (mem_empty_iff_eq_top (f.toElementMap x)).symm
  rw [heq]
  exact (system.isOpen_basicOpen ∅).preimage f.continuous_toElementMap
end

theorem univ_ne_empty : (Set.univ : Set (Fin 1)) ≠ ∅ := by
  intro h
  have h0 : (0 : Fin 1) ∈ (∅ : Set (Fin 1)) := h ▸ Set.mem_univ 0
  simp at h0

section
variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- Approximable map into the Sierpiński system classifying an open set. -/
def openToMap (U : Set V.Element) (hU : IsOpen U) : ApproximableMap V system where
  rel X Y := V.mem X ∧ system.mem Y ∧ (Y = ∅ → ∃ hX : V.mem X, V.principal hX ∈ U)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, system.master_mem, fun heq => (univ_ne_empty (O_master ▸ heq)).elim⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, fY⟩ ⟨_, hY', fY'⟩
    refine ⟨hX, O_inter_mem hY hY', ?_⟩
    intro h
    rcases O_mem.mp hY with rfl | rfl
    · rw [Set.univ_inter] at h; exact fY' h
    · exact fY rfl
  mono := by
    rintro X X' Y Y' ⟨hX, _, fY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    intro hY'eq
    have hYeq : Y = ∅ := Set.subset_empty_iff.mp (hY'eq ▸ hYY')
    obtain ⟨hX0, hmem⟩ := fY hYeq
    have hmem' : V.principal hX ∈ U := hmem
    have hle : V.principal hX ≤ V.principal hX' := (V.principal_le_iff hX hX').mpr hX'X
    exact ⟨hX', V.isOpen_isUpperSet hU hmem' hle⟩

theorem toElementMap_openToMap_principal_mem_empty (U : Set V.Element) (hU : IsOpen U)
    {X : Set γ} (hX : V.mem X) :
    ((openToMap V U hU).toElementMap (V.principal hX)).mem ∅ ↔ V.principal hX ∈ U := by
  rw [← (openToMap V U hU).rel_iff_mem_principal hX]
  constructor
  · rintro ⟨_, _, fimpl⟩
    obtain ⟨_, hmem⟩ := fimpl rfl
    exact hmem
  · intro h
    exact ⟨hX, O_mem_empty, fun _ => ⟨hX, h⟩⟩

theorem mem_mapToOpen_openToMap (U : Set V.Element) (hU : IsOpen U) (x : V.Element) :
    x ∈ mapToOpen V (openToMap V U hU) ↔ x ∈ U := by
  rw [mapToOpen, Set.mem_ofPred_eq, ← mem_empty_iff_eq_top,
    ApproximableMap.toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    rw [toElementMap_openToMap_principal_mem_empty] at hmem
    have hple : V.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact V.isOpen_isUpperSet hU hmem hple
  · intro hxU
    obtain ⟨X, hxX, hXU⟩ := hU.out x hxU
    refine ⟨X, hxX, ?_⟩
    rw [toElementMap_openToMap_principal_mem_empty]
    exact hXU (show V.principal (x.sub hxX) ∈ V.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)

theorem openToMap_mapToOpen (f : ApproximableMap V system) :
    openToMap V (mapToOpen V f) (isOpen_mapToOpen V f) = f := by
  apply ApproximableMap.eq_of_toElementMap_principal
  intro X hX
  apply O_ext
  rw [toElementMap_openToMap_principal_mem_empty, mapToOpen, Set.mem_ofPred_eq,
    ← mem_empty_iff_eq_top]
end

end DomainTheory.NeighbourhoodSystems.O
