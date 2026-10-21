/-ai
Every element of the natural-number domain is either the bottom element or the total element named by a natural number.

If the element contains the singleton of some number, extensionality and the membership law for numerals identify it with that numeral. A neighbourhood of the element is the whole token set, which belongs to the numeral, or a singleton. The same singleton belongs to the numeral. A different singleton meets the chosen one in the empty set, so the element would contain the empty set, which is not a neighbourhood. In the other direction, the master neighbourhood and the chosen singleton belong to the element. If the element contains no singleton, extensionality and the membership law for bottom identify it with bottom. A neighbourhood is then the whole token set, and the master neighbourhood belongs to the element, while a singleton neighbourhood is excluded by the case.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.not_N_mem_empty

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** Element classification: every element of `|N|` is either
the bottom `⊥` or a total element `n̂`. So `N` is the flat domain over `ℕ`. -/
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

end DomainTheory.NeighbourhoodSystems.Exercise418
