module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_8
@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : leastMap L hL hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

theorem rel_interYs {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} (hf : f ∈ stepFun L)
    {X : Set α} (hX : V₀.mem X) : f.rel X (interYs V₁.master L X) := by
  induction L with
  | nil =>
    rw [interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem
  | cons p L ih =>
    have hftail : f ∈ stepFun L := fun q hq => hf q (List.mem_cons.mpr (Or.inr hq))
    have htail := ih hftail
    by_cases hXp : X ⊆ p.1
    · have hp : f.rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel X p.2 := f.mono hp hXp subset_rfl hX (f.rel_cod hp)
      have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]; exact htail

theorem leastMap_le {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hL hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

theorem stepFun_subset_step_iff {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔ interYs V₁.master L X ⊆ Y := by
  constructor
  · intro hsub
    have := hsub (leastMap_mem_stepFun hL hcons)
    exact (mem_step.mp this).2.2
  · intro hsub f hf
    exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

end
end DomainTheory.NeighbourhoodSystems
end
