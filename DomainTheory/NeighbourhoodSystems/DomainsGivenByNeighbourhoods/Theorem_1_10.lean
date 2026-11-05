module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.tokenSystem

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem bracket_inter_nonempty_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    (V.bracket X ∩ V.bracket Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  constructor
  · rintro ⟨x, hxX, hxY⟩
    exact ⟨X ∩ Y, x.sub (x.inter_mem hxX hxY), subset_rfl⟩
  · rintro ⟨Z, hZ, hZsub⟩
    refine ⟨V.principal hZ, ?_, ?_⟩
    · exact ⟨hX, hZsub.trans Set.inter_subset_left⟩
    · exact ⟨hY, hZsub.trans Set.inter_subset_right⟩

/-- Scott's Theorem 1.10: brackets form an isomorphic presentation; clauses (2)–(4) plus the
token-system isomorphism. -/
theorem theorem_110 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) {X Y : Set α},
      V.mem X → V.mem Y →
        ((V.bracket X ∩ V.bracket Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {X Y : Set α},
      V.mem X → V.mem Y → V.bracket X ∩ V.bracket Y = V.bracket (X ∩ Y)) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α), V ≅ᴰ V.tokenSystem) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) {X : Set α} (hX : V.mem X),
      V.principal hX ∈ V.bracket X) :=
  ⟨bracket_inter_nonempty_iff, bracket_inter, isomorphic_tokenSystem, principal_mem_bracket⟩

def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

theorem bracket_nonempty_iff {X : Set α} : (V.bracket X).Nonempty ↔ V.mem X := by
  constructor
  · rintro ⟨x, hx⟩; exact x.sub hx
  · intro hX; exact ⟨V.principal hX, V.principal_mem_bracket hX⟩

end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
