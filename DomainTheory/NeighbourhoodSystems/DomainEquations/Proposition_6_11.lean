module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

def subFam (E : NeighborhoodSystem α) : Set (Set (Set α)) :=
  {𝒮 | ∃ D : NeighborhoodSystem α, D ◁ E ∧ 𝒮 = {X | D.mem X}}

theorem subFam_inter_closed (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X Y : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hXY : E.mem (X ∩ Y)) : X ∩ Y ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.inter_closed hX hY hXY

theorem subFam_master_mem (E : NeighborhoodSystem α) {𝒮 : Set (Set α)}
    (h : 𝒮 ∈ subFam E) : E.master ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  rw [← hD.master_eq]
  exact D.master_mem

theorem subFam_mem_E (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) : E.mem X := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.sub hX

def interSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : NeighborhoodSystem α where
  mem X := ∀ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := fun 𝒮 h𝒮 => subFam_master_mem E (hℱ h𝒮)
  inter_mem := by
    intro X Y Z hX hY hZ hsub 𝒮 h𝒮
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮) (hY 𝒮 h𝒮)
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮) (hZ 𝒮 h𝒮)
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) (E.inter_mem hEX hEY hEZ hsub)
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮))

theorem interSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) :
    {X | (interSys E ℱ hne hℱ).mem X} = ⋂₀ ℱ := by
  ext X
  exact Set.mem_sInter.symm

theorem interSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : interSys E ℱ hne hℱ ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
  inter_closed := by
    intro X Y hX hY hEXY 𝒮 h𝒮
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) hEXY

def ofMem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    NeighborhoodSystem α where
  mem X := X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := subFam_master_mem E h
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    exact subFam_inter_closed E h hX hY
      (E.inter_mem (subFam_mem_E E h hX) (subFam_mem_E E h hY) (subFam_mem_E E h hZ) hsub)
  sub_master := fun hX => E.sub_master (subFam_mem_E E h hX)

theorem ofMem_subsystem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    ofMem E 𝒮 h ◁ E where
  master_eq := rfl
  sub := subFam_mem_E E h
  inter_closed := subFam_inter_closed E h
end

section
set_option linter.unusedVariables false

theorem theorem_611.{u_1} : ∀ {α : Type u_1} (E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (𝒮 : Set (Set α))
  (h :
    @Membership.mem (Set (Set α)) (Set (Set (Set α))) (@Set.instMembership (Set (Set α)))
      (@DomainTheory.NeighbourhoodSystems.Proposition611.subFam α E) 𝒮),
  @DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.Proposition611.ofMem α E 𝒮 h) E :=
  @DomainTheory.NeighbourhoodSystems.Proposition611.ofMem_subsystem
end

end DomainTheory.NeighbourhoodSystems.Proposition611

namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

instance subPartialOrder (E : NeighborhoodSystem α) :
    PartialOrder {D : NeighborhoodSystem α // D ◁ E} where
  le D₀ D₁ := D₀.1 ◁ D₁.1
  le_refl D := Subsystem.refl D.1
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ h₂ := Subtype.ext (h₁.antisymm h₂)
end

end DomainTheory.NeighbourhoodSystems.Proposition611

namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

theorem subFam_nonempty (E : NeighborhoodSystem α) : (subFam E).Nonempty :=
  ⟨{X | E.mem X}, E, Subsystem.refl E, rfl⟩

theorem subFam_sInter_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : ⋂₀ ℱ ∈ subFam E :=
  ⟨interSys E ℱ hne hℱ, interSys_subsystem E ℱ hne hℱ, (interSys_nbset E ℱ hne hℱ).symm⟩

def subIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o {𝒮 : Set (Set α) // 𝒮 ∈ subFam E} where
  toFun D := ⟨{X | D.1.mem X}, ⟨D.1, D.2, rfl⟩⟩
  invFun 𝒮 := ⟨ofMem E 𝒮.1 𝒮.2, ofMem_subsystem E 𝒮.1 𝒮.2⟩
  left_inv := by
    intro D
    apply Subtype.ext
    apply NeighborhoodSystem.ext
    · intro X; exact Iff.rfl
    · exact D.2.master_eq.symm
  right_inv := by
    intro 𝒮
    apply Subtype.ext
    ext X
    exact Iff.rfl
  map_rel_iff' := by
    intro a b
    show ({X | a.1.mem X} : Set (Set α)) ⊆ {X | b.1.mem X} ↔ a.1 ◁ b.1
    constructor
    · intro hsub
      refine (Subsystem.subsystem_iff_subset_of_common a.2 b.2).mpr ?_
      intro X hX
      exact hsub hX
    · intro hsub X hX
      exact hsub.sub hX
end

end DomainTheory.NeighbourhoodSystems.Proposition611

namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

section
variable {α : Type*}

def unionSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    NeighborhoodSystem α where
  mem X := ∃ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_nonempty := E.master_nonempty
  master_mem := by
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact ⟨𝒮, h𝒮, subFam_master_mem E (hℱ h𝒮)⟩
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮z, h𝒮z, hZz⟩ := hZ
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    have hXs : X ∈ 𝒮s := hxs hXx
    have hYs : Y ∈ 𝒮s := hys hYy
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮s) hXs
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮s) hYs
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮z) hZz
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) hXs hYs (E.inter_mem hEX hEY hEZ hsub)⟩
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) hX𝒮)

theorem unionSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    {X | (unionSys E ℱ hne hℱ hdir).mem X} = ⋃₀ ℱ := by
  ext X
  exact Set.mem_sUnion.symm

theorem unionSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    unionSys E ℱ hne hℱ hdir ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact subFam_mem_E E (hℱ h𝒮) hX𝒮
  inter_closed := by
    intro X Y hX hY hEXY
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) (hxs hXx) (hys hYy) hEXY⟩

theorem subFam_sUnion_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    ⋃₀ ℱ ∈ subFam E :=
  ⟨unionSys E ℱ hne hℱ hdir, unionSys_subsystem E ℱ hne hℱ hdir,
    (unionSys_nbset E ℱ hne hℱ hdir).symm⟩
end
end DomainTheory.NeighbourhoodSystems.Proposition611

section
namespace DomainTheory.NeighbourhoodSystems.Proposition611
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222
section
variable {α : Type*}

def subsystemReprIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o
      (reprSystem (subFam E) (subFam_sInter_mem E) (subFam_nonempty E)).Element :=
  (subIso E).trans
    (reprIso (subFam E) (subFam_sInter_mem E) (subFam_nonempty E) (subFam_sUnion_mem E)).symm
end

end DomainTheory.NeighbourhoodSystems.Proposition611
end
