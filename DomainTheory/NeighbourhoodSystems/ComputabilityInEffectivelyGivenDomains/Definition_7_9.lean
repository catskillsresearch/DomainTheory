module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_20

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section
variable {α : Type*} (V : NeighborhoodSystem α)

def PDmem (W : Set (Set α)) : Prop :=
  ∃ L : List (Set α), (∀ X ∈ L, V.mem X) ∧ W = ⋃ X ∈ L, V.upSet X

abbrev dagger : NeighborhoodSystem (Set α) := V.powerSystem

theorem PDmem_union {W₁ W₂ : Set (Set α)} (h₁ : V.PDmem W₁) (h₂ : V.PDmem W₂) :
    V.PDmem (W₁ ∪ W₂) := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  obtain ⟨L₂, hL₂, rfl⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact hL₁ X h
    · exact hL₂ X h
  · ext z
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, List.mem_append]
    constructor
    · rintro (⟨X, hX, hz⟩ | ⟨X, hX, hz⟩)
      · exact ⟨X, Or.inl hX, hz⟩
      · exact ⟨X, Or.inr hX, hz⟩
    · rintro ⟨X, hX | hX, hz⟩
      · exact Or.inl ⟨X, hX, hz⟩
      · exact Or.inr ⟨X, hX, hz⟩

theorem dagger_isomorphic : V ≅ᴰ V.dagger := V.isomorphic_powerSystem

theorem dagger_upSet_inter {X Y Z : Set α} (hX : V.mem X) (hY : V.mem Y) (hZ : V.mem Z)
    (hsub : Z ⊆ X ∩ Y) : V.dagger.mem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  exact ⟨X ∩ Y, V.inter_mem hX hY hZ hsub, rfl⟩

theorem mem_PDunion {L : List (Set α)} {z : Set α} :
    z ∈ (⋃ X ∈ L, V.upSet X) ↔ ∃ X ∈ L, z ∈ V.upSet X := by
  simp only [Set.mem_iUnion, exists_prop]

theorem PDmem_empty : V.PDmem ∅ := by
  refine ⟨[], ?_, ?_⟩
  · intro X hX; cases hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro h; exact absurd h (Set.notMem_empty z)
    · rintro ⟨X, hX, _⟩; cases hX

theorem PDmem_iff_fin {W : Set (Set α)} :
    V.PDmem W ↔ ∃ (n : ℕ) (X : Fin n → Set α),
      (∀ i, V.mem (X i)) ∧ W = ⋃ i, V.upSet (X i) := by
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨L.length, L.get, fun i => hL _ (L.get_mem i), ?_⟩
    ext z
    rw [mem_PDunion, Set.mem_iUnion]
    constructor
    · rintro ⟨X, hX, hz⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hX
      exact ⟨i, hz⟩
    · rintro ⟨i, hz⟩
      exact ⟨L.get i, L.get_mem i, hz⟩
  · rintro ⟨n, X, hX, rfl⟩
    refine ⟨List.ofFn X, ?_, ?_⟩
    · intro Y hY
      obtain ⟨i, rfl⟩ := Set.mem_range.mp (List.mem_ofFn.mp hY)
      exact hX i
    · ext z
      rw [Set.mem_iUnion, mem_PDunion]
      constructor
      · rintro ⟨i, hz⟩
        exact ⟨X i, List.mem_ofFn.mpr (Set.mem_range.mpr ⟨i, rfl⟩), hz⟩
      · rintro ⟨Y, hY, hz⟩
        obtain ⟨i, rfl⟩ := Set.mem_range.mp (List.mem_ofFn.mp hY)
        exact ⟨i, hz⟩

theorem PDmem_upSet {X : Set α} (hX : V.mem X) : V.PDmem (V.upSet X) := by
  refine ⟨[X], ?_, ?_⟩
  · intro Y hY; rw [List.mem_singleton] at hY; subst hY; exact hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro hz; exact ⟨X, List.mem_singleton.mpr rfl, hz⟩
    · rintro ⟨Y, hY, hz⟩; rw [List.mem_singleton] at hY; subst hY; exact hz

theorem PDmem_master : V.PDmem (V.upSet V.master) := V.PDmem_upSet V.master_mem

theorem upSet_inter_nonempty_iff {X Y : Set α} :
    (V.upSet X ∩ V.upSet Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  rw [V.upSet_inter]
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩

end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
