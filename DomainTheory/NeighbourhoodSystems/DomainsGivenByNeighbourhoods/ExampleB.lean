module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.BitDom

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone.trichotomy σ τ

def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ
    ⟨[], Set.mem_univ _⟩ ⟨[], cone.nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

@[simp] theorem B_master : B.master = Set.univ := rfl

theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, cone.mem]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

theorem memB_prepend (σ : Str) {X : Set Str} (hX : B.mem X) : B.mem (prepend σ X) := by
  obtain ⟨ρ, rfl⟩ := hX
  exact ⟨σ ++ ρ, prepend_cone σ ρ⟩

@[simp] theorem prepend_nil (X : Set Str) : prepend [] X = X := by
  ext w; simp [mem_prepend]

def sigmaBot (σ : Str) : B.Element := B.principal (memB_cone σ)

def sigmaElt (σ : Str) (x : B.Element) : B.Element where
  mem Y := B.mem Y ∧ ∃ X, x.mem X ∧ prepend σ X ⊆ Y
  sub h := h.1
  master_mem := ⟨B.master_mem, B.master, x.master_mem, Set.subset_univ _⟩
  inter_mem := by
    intro Y₁ Y₂ h1 h2
    obtain ⟨hY₁, X₁, hX₁, hsub₁⟩ := h1
    obtain ⟨hY₂, X₂, hX₂, hsub₂⟩ := h2
    have hXinter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁ hX₂
    have hsub : prepend σ (X₁ ∩ X₂) ⊆ Y₁ ∩ Y₂ := by
      rintro w ⟨τ, ⟨hτ₁, hτ₂⟩, rfl⟩
      exact ⟨hsub₁ ⟨τ, hτ₁, rfl⟩, hsub₂ ⟨τ, hτ₂, rfl⟩⟩
    have hZmem : B.mem (prepend σ (X₁ ∩ X₂)) := memB_prepend σ (x.sub hXinter)
    exact ⟨B.inter_mem hY₁ hY₂ hZmem hsub, X₁ ∩ X₂, hXinter, hsub⟩
  up_mem := by
    intro X Y hX hY hXY
    obtain ⟨_, X', hX', hsub'⟩ := hX
    exact ⟨hY, X', hX', hsub'.trans hXY⟩

theorem bot_mem_cone_iff {σ : Str} : B.bot.mem (cone σ) ↔ σ = [] := by
  rw [mem_bot, B_master, ← cone.nil]
  constructor
  · exact cone.injective
  · intro h; rw [h]

end DomainTheory.NeighbourhoodSystems.BitDom
