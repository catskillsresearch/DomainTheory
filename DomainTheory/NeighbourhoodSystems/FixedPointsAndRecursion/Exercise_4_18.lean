module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_3

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise418
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43

section
/-- Distinct singletons are disjoint. -/
theorem singleton_inter_eq_empty {n m : ℕ} (hmn : m ≠ n) :
    ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h2
  exact hmn h2.symm
end

section
end
end DomainTheory.NeighbourhoodSystems.Exercise418

section
namespace DomainTheory.NeighbourhoodSystems.Exercise418
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43
section
/- concordance: source L2321 EXERCISE 4.18 checking the number domain -/
/-- **Exercise 4.18 (Scott 1981, PRG-19).** The numerals are distinct: `n̂ = m̂ ⟹ n = m`. -/
theorem natElem_injective {n m : ℕ} (h : natElem n = natElem m) : n = m := by
  have hmem : (natElem m).mem {n} := h ▸ (mem_natElem_iff.mpr (Or.inr rfl))
  rw [mem_natElem_iff] at hmem
  rcases hmem with hu | hs
  · exact absurd hu (singleton_ne_univ n)
  · exact singleton_nat_inj hs
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not a numeral successor. -/
theorem natElem_zero_ne_succ (k : ℕ) : natElem 0 ≠ natElem (k + 1) := fun h =>
  Nat.succ_ne_zero k (natElem_injective h).symm
end

section
/-- `∅` is not a neighbourhood of `N`. -/
theorem not_N_mem_empty : ¬ N.mem (∅ : Set ℕ) := by
  rw [N_mem]
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact (Set.singleton_ne_empty n) h.symm
end

section
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
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** `succ` is injective on the total elements. -/
theorem succMap_injective {n m : ℕ}
    (h : succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m)) : n = m := by
  rw [succMap_natElem, succMap_natElem] at h
  have := natElem_injective h
  omega
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not in the image of `succ` — Peano's
"zero is not a successor". -/
theorem zero_ne_succMap (n : ℕ) : natElem 0 ≠ succMap.toElementMap (natElem n) := by
  rw [succMap_natElem]
  exact natElem_zero_ne_succ n
end

section
set_option linter.unusedVariables false

theorem example_418 : And
  (And
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m))
  (∀ (n : Nat),
    @Ne
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
        DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))) :=
  @And.intro
  (And
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m))
  (∀ (n : Nat),
    @Ne
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
        DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
  (@And.intro
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m)
    (@And.intro
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@And.intro
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m)
        DomainTheory.NeighbourhoodSystems.Exercise418.element_classification
        @DomainTheory.NeighbourhoodSystems.Exercise418.natElem_injective)
      DomainTheory.NeighbourhoodSystems.Exercise418.natElem_zero_ne_succ)
    @DomainTheory.NeighbourhoodSystems.Exercise418.succMap_injective)
  DomainTheory.NeighbourhoodSystems.Exercise418.zero_ne_succMap
end

end DomainTheory.NeighbourhoodSystems.Exercise418
end
