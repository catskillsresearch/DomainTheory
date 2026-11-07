module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.TwoToken

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.TwoToken

namespace neighborhoodSystem

open NeighborhoodSystem

def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    intro X Y hX hY
    rw [hX, hY, master_inter]
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

def elemOne : neighborhoodSystem.Element where
  mem X := X = master ∨ X = one
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_one
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hXY one_not_subset_zero
      · exact Or.inr rfl

end neighborhoodSystem
theorem zero_not_subset_one : ¬zero ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [zero])
  simp [one] at this

namespace neighborhoodSystem

open NeighborhoodSystem

def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = zero
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_zero
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hXY zero_not_subset_one

end neighborhoodSystem
theorem zero_ne_master : zero ≠ master := by
  intro h
  have : (1 : Token) ∈ zero := h ▸ (by simp [master])
  simp [zero] at this

theorem one_ne_master : one ≠ master := by
  intro h
  have : (0 : Token) ∈ one := h ▸ (by simp [master])
  simp [one] at this

namespace neighborhoodSystem

open NeighborhoodSystem

theorem mem_zero_of_mem (x : neighborhoodSystem.Element) (h : x.mem zero) :
    x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · exact Or.inr hzero
    · have hxone : x.mem one := hone ▸ hx
      have := x.inter_mem h hxone
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

theorem mem_one_of_mem (x : neighborhoodSystem.Element) (h : x.mem one) :
    x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · have hxzero : x.mem zero := hzero ▸ hx
      have := x.inter_mem hxzero h
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
    · exact Or.inr hone
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

theorem zero_ne_one : zero ≠ (one : Set Token) := by
  intro h
  have h0 : (0 : Token) ∈ zero := by simp [zero]
  rw [h] at h0
  simp [one] at h0

open NeighborhoodSystem

theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem one := h one (Or.inr rfl)
    have hm : one = master := this
    exact one_ne_master hm

theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem zero := h zero (Or.inr rfl)
    have hm : zero = master := this
    exact zero_ne_master hm

theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne := by
  by_cases h0 : x.mem zero
  · exact Or.inr (Or.inl (mem_zero_of_mem x h0))
  by_cases h1 : x.mem one
  · exact Or.inr (Or.inr (mem_one_of_mem x h1))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · rfl
    · exact absurd (hzero ▸ hx) h0
    · exact absurd (hone ▸ hx) h1
  · intro hx
    rw [hx]
    exact x.master_mem

theorem bot_is_unique_partial (x : neighborhoodSystem.Element) :
    x ≠ elemZero → x ≠ elemOne → x = bot := by
  intro hne0 hne1
  rcases element_classification x with hx | hx | hx
  · exact hx
  · exact (hne0 hx).elim
  · exact (hne1 hx).elim

theorem not_elemOne_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h one (Or.inr rfl) with h' | h'
  · exact one_ne_master h'
  · exact zero_ne_one h'.symm

theorem not_elemZero_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h zero (Or.inr rfl) with h' | h'
  · exact zero_ne_master h'
  · exact zero_ne_one h'

theorem eq_bot_of_le_elemZero_of_le_elemOne {a : neighborhoodSystem.Element}
    (h0 : a ≤ elemZero) (h1 : a ≤ elemOne) : a = bot := by
  rcases element_classification a with rfl | rfl | rfl
  · rfl
  · exact absurd h1 not_elemZero_le_elemOne
  · exact absurd h0 not_elemOne_le_elemZero

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.TwoToken
