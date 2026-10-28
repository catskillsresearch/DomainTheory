module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise114
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

def mem (X : Set ℕ) : Prop := X = Set.univ ∨ (X.Finite ∧ X.Nonempty)

theorem nonempty_of_mem {X : Set ℕ} (h : mem X) : X.Nonempty := by
  rcases h with rfl | h
  · exact Set.univ_nonempty
  · exact h.2

def neighborhoodSystem : NeighborhoodSystem ℕ where
  mem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hne : (X ∩ Y).Nonempty := (nonempty_of_mem hZ).mono hZsub
    rcases hX with hX | hX
    · rw [hX, Set.univ_inter]; exact hY
    · rcases hY with hY | hY
      · rw [hY, Set.inter_univ]; exact Or.inr hX
      · exact Or.inr ⟨hX.1.inter_of_left Y, hne⟩
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ mem X := Iff.rfl

def bot : neighborhoodSystem.Element := neighborhoodSystem.bot

def fin {X : Set ℕ} (h : neighborhoodSystem.mem X) : neighborhoodSystem.Element :=
  neighborhoodSystem.principal h

theorem empty_not_mem : ¬ mem (∅ : Set ℕ) := by
  rintro (h | ⟨_, h⟩)
  · exact Set.empty_ne_univ h
  · exact Set.not_nonempty_empty h

theorem mem_singleton (n : ℕ) : mem {n} :=
  Or.inr ⟨Set.finite_singleton n, Set.singleton_nonempty n⟩

theorem singleton_isTotal (n : ℕ) :
    neighborhoodSystem.IsTotal (neighborhoodSystem.principal (mem_singleton n)) := by
  intro y hy W hW
  have hn : y.mem {n} := hy {n} ⟨mem_singleton n, subset_rfl⟩
  refine ⟨y.sub hW, ?_⟩
  by_contra hc
  rw [Set.singleton_subset_iff] at hc
  have hempty : ({n} : Set ℕ) ∩ W = (∅ : Set ℕ) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hk⟩
    exact hc hk
  have hi := y.inter_mem hn hW
  rw [hempty] at hi
  exact empty_not_mem (y.sub hi)

section
set_option linter.unusedVariables false

theorem example_114 : ∀ (n : Nat),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
    DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Nat
      DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
      (@Singleton.singleton Nat (Set Nat) (@Set.instSingletonSet Nat) n)
      (DomainTheory.NeighbourhoodSystems.Exercise114.mem_singleton n)) :=
  DomainTheory.NeighbourhoodSystems.Exercise114.singleton_isTotal
end
end

end DomainTheory.NeighbourhoodSystems.Exercise114
end
