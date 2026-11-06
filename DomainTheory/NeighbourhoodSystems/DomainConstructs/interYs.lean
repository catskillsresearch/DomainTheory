module

public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

variable {α β : Type*}

def interYs (m : Set β) : List (Set α × Set β) → Set α → Set β
  | [], _ => m
  | p :: L, X => {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X

@[simp] theorem interYs_nil (m : Set β) (X : Set α) : interYs m [] X = m := rfl

theorem interYs_cons (m : Set β) (p : Set α × Set β) (L : List (Set α × Set β)) (X : Set α) :
    interYs m (p :: L) X = {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X := rfl

theorem mem_interYs {m : Set β} {L : List (Set α × Set β)} {X : Set α} {z : β} :
    z ∈ interYs m L X ↔ z ∈ m ∧ ∀ p ∈ L, X ⊆ p.1 → z ∈ p.2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [interYs_cons]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hp, hm, hL⟩
      refine ⟨hm, ?_⟩
      rintro q (rfl | hq) hXq
      · exact hp hXq
      · exact hL q hq hXq
    · rintro ⟨hm, hall⟩
      exact ⟨fun hXp => hall p (Or.inl rfl) hXp, hm,
        fun q hq hXq => hall q (Or.inr hq) hXq⟩

theorem interYs_antitone {m : Set β} {L : List (Set α × Set β)} {X X' : Set α} (h : X' ⊆ X) :
    interYs m L X' ⊆ interYs m L X := by
  intro z hz
  rw [mem_interYs] at hz ⊢
  exact ⟨hz.1, fun p hp hXp => hz.2 p hp (h.trans hXp)⟩

theorem interYs_subset_master {m : Set β} {L : List (Set α × Set β)} {X : Set α} :
    interYs m L X ⊆ m := fun _ hz => (mem_interYs.mp hz).1

theorem interYs_subset_of_mem {m : Set β} {L : List (Set α × Set β)} {p : Set α × Set β}
    (hp : p ∈ L) : interYs m L p.1 ⊆ p.2 :=
  fun _ hz => (mem_interYs.mp hz).2 p hp subset_rfl

end DomainTheory.NeighbourhoodSystems
