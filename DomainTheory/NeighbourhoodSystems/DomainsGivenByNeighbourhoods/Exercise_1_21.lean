module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.tokenSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_19
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5a

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

theorem bracket_nonempty_iff {X : Set α} : (V.bracket X).Nonempty ↔ V.mem X := by
  constructor
  · rintro ⟨x, hx⟩; exact x.sub hx
  · intro hX; exact ⟨V.principal hX, V.principal_mem_bracket hX⟩

theorem consistent_iff_bracket_interUpTo_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty := by
  rw [V.consistent_iff_interUpTo_mem X hX]
  exact V.bracket_nonempty_iff.symm

theorem consistent_iff_iInter_bracket_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ ∃ x : V.Element, ∀ i, i < n → x ∈ V.bracket (X i) := by
  rw [V.consistent_iff_bracket_interUpTo_nonempty X hX]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i hi => x.up_mem hx (hX i hi) (interUpTo.subset V X hi)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.mem_interUpTo X (fun i hi => hx i hi)⟩

theorem tokenSystem_complete : V.tokenSystem.IsComplete := by
  intro y
  refine ⟨V.ofToken y, ?_, ?_⟩
  · rintro S ⟨W, hW, rfl⟩
    constructor
    · intro hyW; exact ⟨hW, hyW⟩
    · rintro ⟨_, hyW⟩; exact hyW
  · intro b hb
    apply Element.ext
    intro W
    by_cases hW : V.mem W
    · have hb' := hb (V.bracket W) ⟨W, hW, rfl⟩
      constructor
      · intro hbW; exact ⟨hW, hb'.mpr hbW⟩
      · intro hxW; exact hb'.mp hxW.2
    · constructor
      · intro hbW; exact absurd (b.sub hbW) hW
      · intro hxW; exact absurd ((V.ofToken y).sub hxW) hW

theorem tokenSystem_isPositive : V.tokenSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.bracket_inter hX hY]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨V.principal hW, V.principal_mem_bracket hW⟩
  · rintro ⟨x, hx⟩
    exact ⟨X ∩ Y, x.sub hx, rfl⟩

theorem tokenSystem_toToken_bijective : Function.Bijective V.toToken :=
  V.tokenIso.bijective

theorem exercise_1_21 :
    (∀ (X : ℕ → Set α) {n : ℕ}, (∀ i, i < n → V.mem (X i)) →
        (V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty)) ∧
      (∀ (X : ℕ → Set α) {n : ℕ}, (∀ i, i < n → V.mem (X i)) →
        (V.Consistent X n ↔ ∃ x, ∀ i, i < n → x ∈ V.bracket (X i))) ∧
      V.tokenSystem.IsComplete ∧
      V.tokenSystem.IsPositive ∧
      Function.Bijective V.toToken :=
  ⟨V.consistent_iff_bracket_interUpTo_nonempty, V.consistent_iff_iInter_bracket_nonempty,
    V.tokenSystem_complete, V.tokenSystem_isPositive, V.tokenSystem_toToken_bijective⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
