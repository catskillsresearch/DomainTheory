module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.numberDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise418
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43

section

theorem singleton_inter_eq_empty {n m : ℕ} (hmn : m ≠ n) :
    ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h2
  exact hmn h2.symm
end

end DomainTheory.NeighbourhoodSystems.Exercise418

section
namespace DomainTheory.NeighbourhoodSystems.Exercise418
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43
section

theorem natElem_injective {n m : ℕ} (h : natElem n = natElem m) : n = m := by
  have hmem : (natElem m).mem {n} := h ▸ (mem_natElem_iff.mpr (Or.inr rfl))
  rw [mem_natElem_iff] at hmem
  rcases hmem with hu | hs
  · exact absurd hu (singleton_ne_univ n)
  · exact singleton_nat_inj hs
end

section

theorem natElem_zero_ne_succ (k : ℕ) : natElem 0 ≠ natElem (k + 1) := fun h =>
  Nat.succ_ne_zero k (natElem_injective h).symm
end

section

theorem not_N_mem_empty : ¬ N.mem (∅ : Set ℕ) := by
  rw [N_mem]
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact (Set.singleton_ne_empty n) h.symm
end

section

theorem element_classification (x : N.Element) :
    x = N.bot ∨ ∃ n, x = natElem n := by
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    apply Element.ext
    intro Y
    rw [mem_natElem_iff]
    constructor
    · intro hY
      rcases N_mem.mp (x.sub hY) with rfl | ⟨m, rfl⟩
      · exact Or.inl rfl
      · by_cases hmn : m = n
        · subst hmn; exact Or.inr rfl
        · exfalso
          have hmem := x.inter_mem hn hY
          rw [singleton_inter_eq_empty hmn] at hmem
          exact not_N_mem_empty (x.sub hmem)
    · rintro (rfl | rfl)
      · exact x.master_mem
      · exact hn
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    rw [N_bot_mem]
    constructor
    · intro hY
      rcases N_mem.mp (x.sub hY) with rfl | ⟨m, rfl⟩
      · rfl
      · exact absurd hY (fun hm => h ⟨m, hm⟩)
    · rintro rfl
      exact x.master_mem
end

section

theorem succMap_injective {n m : ℕ}
    (h : succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m)) : n = m := by
  rw [succMap_natElem, succMap_natElem] at h
  have := natElem_injective h
  omega
end

section

theorem zero_ne_succMap (n : ℕ) : natElem 0 ≠ succMap.toElementMap (natElem n) := by
  rw [succMap_natElem]
  exact natElem_zero_ne_succ n
end

section

theorem example_418 :
    (∀ x : N.Element, x = N.bot ∨ ∃ n, x = natElem n) ∧
    (∀ {n m : ℕ}, natElem n = natElem m → n = m) ∧
    (∀ k : ℕ, natElem 0 ≠ natElem (k + 1)) ∧
    (∀ {n m : ℕ},
      succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m) → n = m) ∧
    (∀ n : ℕ, natElem 0 ≠ succMap.toElementMap (natElem n)) :=
  ⟨element_classification, @natElem_injective, natElem_zero_ne_succ,
    @succMap_injective, zero_ne_succMap⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise418
end
