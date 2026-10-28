module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_3
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_4
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example_1_5

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem eq_principal_of_minimum (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZ, hXZ⟩
    exact x.up_mem hX hZ hXZ

theorem exists_minimum_of_fintype [Fintype α] (x : V.Element) :
    ∃ X, x.mem X ∧ ∀ Y, x.mem Y → X ⊆ Y := by
  classical
  suffices aux : ∀ n (A : Set α), A.ncard = n → x.mem A →
      ∃ X, x.mem X ∧ X ⊆ A ∧ ∀ Y, x.mem Y → Y ⊆ A → X ⊆ Y from by
    obtain ⟨X, hX, _, hmin⟩ := aux V.master.ncard V.master rfl x.master_mem
    exact ⟨X, hX, fun Y hY => hmin Y hY (V.sub_master (x.sub hY))⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn hA
    by_cases hleast : ∀ Y, x.mem Y → Y ⊆ A → A ⊆ Y
    · exact ⟨A, hA, subset_rfl, hleast⟩
    · push Not at hleast
      obtain ⟨Y, hY, hYA, hAY⟩ := hleast
      have hss : Y ⊂ A := ⟨hYA, hAY⟩
      have hlt : Y.ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hss
      obtain ⟨X, hX, hXsub, hmin⟩ := ih Y.ncard hlt Y rfl hY
      refine ⟨X, hX, hXsub.trans hYA, ?_⟩
      intro Z hZ hZA
      have hcap : x.mem (Z ∩ Y) := x.inter_mem hZ hY
      exact (hmin (Z ∩ Y) hcap Set.inter_subset_right).trans Set.inter_subset_left

theorem element_eq_principal_of_fintype [Fintype α] (x : V.Element) :
    ∃ X, ∃ hX : V.mem X, x = V.principal hX := by
  obtain ⟨X, hX, hmin⟩ := V.exists_minimum_of_fintype x
  exact ⟨X, x.sub hX, V.eq_principal_of_minimum x hX hmin⟩

theorem smaller_neighbourhood_le {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hY ≤ V.principal hX ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h Y ⟨hY, subset_rfl⟩).2
  · intro hXY Z hZ
    exact ⟨hZ.1, hXY.trans hZ.2⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example12
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example13
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example14
namespace DomainTheory.NeighbourhoodSystems.Example15

theorem element_eq_principal (x : neighborhoodSystem.Element) :
    ∃ X, ∃ hX : neighborhoodSystem.mem X, x = neighborhoodSystem.principal hX :=
  NeighborhoodSystem.element_eq_principal_of_fintype neighborhoodSystem x

end DomainTheory.NeighbourhoodSystems.Example15
namespace DomainTheory.NeighbourhoodSystems.ExampleB
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

abbrev Str := List Bool

def cone (σ : Str) : Set Str := {w | σ <+: w}

@[simp] theorem mem_cone {σ w : Str} : w ∈ cone σ ↔ σ <+: w := Iff.rfl

theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone_trichotomy σ τ

def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ
    ⟨[], Set.mem_univ _⟩ ⟨[], cone_nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

@[simp] theorem B_master : B.master = Set.univ := rfl

theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
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

theorem cone_injective {σ τ : Str} (h : cone σ = cone τ) : σ = τ := by
  have h1 : τ <+: σ := cone_subset_cone.mp (le_of_eq h)
  have h2 : σ <+: τ := cone_subset_cone.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

theorem bot_mem_cone_iff {σ : Str} : B.bot.mem (cone σ) ↔ σ = [] := by
  rw [mem_bot, B_master, ← cone_nil]
  constructor
  · exact cone_injective
  · intro h; rw [h]
end

end DomainTheory.NeighbourhoodSystems.ExampleB
end
