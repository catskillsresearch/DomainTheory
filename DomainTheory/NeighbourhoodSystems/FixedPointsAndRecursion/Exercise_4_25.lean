module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_3
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section

def shift (X : Set ℕ) : Set ℕ := {k | ∃ m ∈ X, k = m + 1}
end

section

def tail (n : ℕ) : Set ℕ := {m | n ≤ m}
end

section
@[simp] theorem mem_tail {n k : ℕ} : k ∈ tail n ↔ n ≤ k := Iff.rfl
end

section

def memC1 (X : Set ℕ) : Prop := (∃ n, X = tail n) ∨ (∃ n, X = {n})
end

section
theorem memC1_singleton (n : ℕ) : memC1 ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩
end

section
theorem memC1_tail (n : ℕ) : memC1 (tail n) := Or.inl ⟨n, rfl⟩
end

section
theorem shift_mono {X X' : Set ℕ} (h : X' ⊆ X) : shift X' ⊆ shift X := by
  rintro k ⟨m, hm, rfl⟩; exact ⟨m, h hm, rfl⟩
end

section

theorem shift_singleton (n : ℕ) : shift ({n} : Set ℕ) = {n + 1} := by
  ext k
  simp only [shift, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨n, rfl, rfl⟩
end

section

theorem shift_tail (n : ℕ) : shift (tail n) = tail (n + 1) := by
  ext k
  simp only [shift, tail, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨k - 1, by omega, by omega⟩
end

section

theorem memC1_shift {X : Set ℕ} (hX : memC1 X) : memC1 (shift X) := by
  rcases hX with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact Or.inl ⟨n + 1, shift_tail n⟩
  · exact Or.inr ⟨n + 1, shift_singleton n⟩
end

section

theorem singleton_tail_nd (n k : ℕ) :
    ({k} : Set ℕ) ⊆ tail n ∨ tail n ⊆ {k} ∨ ({k} : Set ℕ) ∩ tail n = ∅ := by
  by_cases h : n ≤ k
  · exact Or.inl (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_tail, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hw; exact h hw
end

section

theorem nestedOrDisjoint : NestedOrDisjoint memC1 := by
  rintro X Y (⟨n, rfl⟩ | ⟨n, rfl⟩) (⟨m, rfl⟩ | ⟨m, rfl⟩)
  · rcases le_total n m with h | h
    · exact Or.inr (Or.inl (fun k hk => le_trans h hk))
    · exact Or.inl (fun k hk => le_trans h hk)
  · rcases singleton_tail_nd n m with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_tail_nd m n with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2; exact h h2
end

section
theorem tail_zero : tail 0 = Set.univ := by ext k; simp [tail]
end

section
theorem memC1_univ : memC1 (Set.univ : Set ℕ) := Or.inl ⟨0, tail_zero.symm⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise425

section
namespace DomainTheory.NeighbourhoodSystems.Exercise425
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
section

def C1 : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memC1 Set.univ Set.univ_nonempty
    memC1_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)
end

section
@[simp] theorem C1_mem {X : Set ℕ} : C1.mem X ↔ memC1 X := Iff.rfl
end

section
@[simp] theorem C1_master : C1.master = (Set.univ : Set ℕ) := rfl
end

section

def consMap : ApproximableMap C1 C1 where
  rel X Y := memC1 X ∧ memC1 Y ∧ shift X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨memC1_univ, memC1_univ, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : shift X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, C1.inter_mem hY hY' (memC1_shift hX) hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (shift_mono hX'X).trans (hsub.trans hYY')⟩
end

section

def infElt : C1.Element := consMap.fixElement
end

section

def oneBot (n : ℕ) : C1.Element := C1.principal (memC1_tail n)
end

section

def oneElem (n : ℕ) : C1.Element := C1.principal (memC1_singleton n)
end

section

def relateNToC1 : ApproximableMap Example43.N C1 := Example43.constLiftN C1 oneElem
end

section

theorem consMap_oneBot (n : ℕ) : consMap.toElementMap (oneBot n) = oneBot (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift (tail n) ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_tail] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨tail n, ⟨memC1_tail n, subset_rfl⟩, memC1_tail n, hY, ?_⟩
    rw [shift_tail]; exact hsub
end

section

theorem consMap_oneElem (n : ℕ) : consMap.toElementMap (oneElem n) = oneElem (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift {n} ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{n}, ⟨memC1_singleton n, subset_rfl⟩, memC1_singleton n, hY, ?_⟩
    rw [shift_singleton]; exact hsub
end

section

theorem infElt_eq : consMap.toElementMap infElt = infElt :=
  toElementMap_fixElement consMap
end

section

theorem relateNToC1_bot : relateNToC1.toElementMap Example43.N.bot = C1.bot :=
  Example43.constLiftN_bot C1 oneElem
end

section
set_option linter.unusedVariables false

theorem example_425 : @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Exercise425.C1)
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
    DomainTheory.NeighbourhoodSystems.Exercise425.C1 DomainTheory.NeighbourhoodSystems.Exercise425.relateNToC1
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat DomainTheory.NeighbourhoodSystems.Example43.N))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat DomainTheory.NeighbourhoodSystems.Exercise425.C1) :=
  DomainTheory.NeighbourhoodSystems.Exercise425.relateNToC1_bot
end

section

theorem relateNToC1_natElem (n : ℕ) :
    relateNToC1.toElementMap (Example43.natElem n) = oneElem n :=
  Example43.constLiftN_natElem C1 oneElem n
end

end DomainTheory.NeighbourhoodSystems.Exercise425
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
open ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

theorem fixMap_fixed (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixMap V).toElementMap φ) = (fixMap V).toElementMap φ := by
  rw [fixMap_toElementMap]
  exact toElementMap_fixElement (toApproxMap φ)

theorem fixMap_unique (V : NeighborhoodSystem α) (fax : ApproximableMap (funSpace V V) V)
    (h_fix : ∀ φ, (toApproxMap φ).toElementMap (fax.toElementMap φ) = fax.toElementMap φ)
    (h_least : ∀ (φ : (funSpace V V).Element) (z : V.Element),
      (toApproxMap φ).toElementMap z ≤ z → fax.toElementMap φ ≤ z) :
    fax = fixMap V := by
  apply ext_of_toElementMap
  intro φ
  apply le_antisymm
  · exact h_least φ _ (le_of_eq (fixMap_fixed V φ))
  · exact fixMap_least V φ (le_of_eq (h_fix φ))

end

end DomainTheory.NeighbourhoodSystems
end
