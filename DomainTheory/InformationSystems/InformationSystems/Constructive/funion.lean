module

public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

theorem insert_comm' (a b : α) (s : Finset α) :
    insert a (insert b s) = insert b (insert a s) := by
  ext x
  simp only [Finset.mem_insert]
  constructor
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

instance instLeftCommutativeInsert :
    LeftCommutative (insert : α → Finset α → Finset α) := ⟨insert_comm'⟩

def funion (u v : Finset α) : Finset α := Multiset.foldr insert u v.1

@[inherit_doc] infixl:65 " ∪' " => funion

namespace decidableEq_finset

omit [DecidableEq α] in
theorem eq_of_subset (s t : Finset α) (h : s ⊆ t ∧ t ⊆ s) : s = t :=
  Finset.Subset.antisymm h.1 h.2

omit [DecidableEq α] in
theorem false_of_ne (s t : Finset α) (h : ¬(s ⊆ t ∧ t ⊆ s)) (heq : s = t) :
    False := by
  subst heq
  exact h ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

end decidableEq_finset

def decidableEq_finset {α : Type*} [DecidableEq α] : DecidableEq (Finset α) :=
  fun s t =>
    if h : s ⊆ t ∧ t ⊆ s then
      isTrue (decidableEq_finset.eq_of_subset s t h)
    else
      isFalse (decidableEq_finset.false_of_ne s t h)

namespace funion

theorem mem_foldr_insert (a : α) (u : Finset α) (s : Multiset α) :
    a ∈ Multiset.foldr insert u s ↔ a ∈ u ∨ a ∈ s := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro b t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
    · rintro (h | h | h)
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

@[simp] theorem mem {a : α} {u v : Finset α} :
    a ∈ u ∪' v ↔ a ∈ u ∨ a ∈ v := mem_foldr_insert a u v.1

@[simp] theorem empty_right (u : Finset α) : u ∪' (∅ : Finset α) = u := by
  ext x
  simp only [mem, Finset.notMem_empty, or_false]

theorem subset_left (u v : Finset α) : u ⊆ u ∪' v := fun _ hx => mem.2 (Or.inl hx)

theorem subset_right (u v : Finset α) : v ⊆ u ∪' v := fun _ hx => mem.2 (Or.inr hx)

theorem subset_iff {u v w : Finset α} : u ∪' v ⊆ w ↔ u ⊆ w ∧ v ⊆ w := by
  constructor
  · intro h
    exact ⟨fun x hx => h (subset_left u v hx),
           fun x hx => h (subset_right u v hx)⟩
  · rintro ⟨hu, hv⟩ x hx
    rcases mem.1 hx with h | h
    exacts [hu h, hv h]

theorem coe (u v : Finset α) :
    (↑(u ∪' v) : Set α) = (↑u : Set α) ∪ ↑v := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem]

theorem insert (u : Finset α) (a : α) (t : Finset α) :
    u ∪' insert a t = insert a (u ∪' t) := by
  ext x
  constructor
  · intro hx
    rcases mem.mp hx with hu | hins
    · exact Finset.mem_insert_of_mem (mem.mpr (Or.inl hu))
    · rcases Finset.mem_insert.mp hins with ha | ht
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert_of_mem (mem.mpr (Or.inr ht))
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | h
    · exact mem.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl ha)))
    · rcases mem.mp h with hu | ht
      · exact mem.mpr (Or.inl hu)
      · exact mem.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ht)))

theorem singleton_eq_insert (a : α) (s : Finset α) :
    ({a} : Finset α) ∪' s = Insert.insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem.mp hx with ha | hs
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp ha))
    · exact Finset.mem_insert_of_mem hs
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | hs
    · exact mem.mpr (Or.inl (Finset.mem_singleton.mpr ha))
    · exact mem.mpr (Or.inr hs)

end funion

end DomainTheory.InformationSystems.Constructive
