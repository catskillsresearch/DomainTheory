module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.numberDomain
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.UnarySeq
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

def shift (X : Set ℕ) : Set ℕ := {k | ∃ m ∈ X, k = m + 1}

def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

@[simp] theorem mem_tail {n k : ℕ} : k ∈ tail n ↔ n ≤ k := Iff.rfl

def memC1 (X : Set ℕ) : Prop := (∃ n, X = tail n) ∨ (∃ n, X = {n})

theorem memC1_singleton (n : ℕ) : memC1 ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩

theorem memC1_tail (n : ℕ) : memC1 (tail n) := Or.inl ⟨n, rfl⟩

theorem shift_mono {X X' : Set ℕ} (h : X' ⊆ X) : shift X' ⊆ shift X := by
  rintro k ⟨m, hm, rfl⟩; exact ⟨m, h hm, rfl⟩

theorem shift_singleton (n : ℕ) : shift ({n} : Set ℕ) = {n + 1} := by
  ext k
  simp only [shift, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨n, rfl, rfl⟩

theorem shift_tail (n : ℕ) : shift (tail n) = tail (n + 1) := by
  ext k
  simp only [shift, tail, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨k - 1, by omega, by omega⟩

theorem memC1_shift {X : Set ℕ} (hX : memC1 X) : memC1 (shift X) := by
  rcases hX with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact Or.inl ⟨n + 1, shift_tail n⟩
  · exact Or.inr ⟨n + 1, shift_singleton n⟩

theorem singleton_tail_nd (n k : ℕ) :
    ({k} : Set ℕ) ⊆ tail n ∨ tail n ⊆ {k} ∨ ({k} : Set ℕ) ∩ tail n = ∅ := by
  by_cases h : n ≤ k
  · exact Or.inl (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_tail, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hw; exact h hw

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

theorem tail_zero : tail 0 = Set.univ := by ext k; simp [tail]

theorem memC1_univ : memC1 (Set.univ : Set ℕ) := Or.inl ⟨0, tail_zero.symm⟩

end DomainTheory.NeighbourhoodSystems.UnarySeq
namespace DomainTheory.NeighbourhoodSystems.UnarySeq
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

def C1 : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memC1 Set.univ Set.univ_nonempty
    memC1_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem C1_mem {X : Set ℕ} : C1.mem X ↔ memC1 X := Iff.rfl

@[simp] theorem C1_master : C1.master = (Set.univ : Set ℕ) := rfl

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

def infElt : C1.Element := consMap.fixElement

def oneBot (n : ℕ) : C1.Element := C1.principal (memC1_tail n)

def oneElem (n : ℕ) : C1.Element := C1.principal (memC1_singleton n)

def relateNToC1 : ApproximableMap NatDom.N C1 := NatDom.constLiftN C1 oneElem

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

theorem infElt_eq : consMap.toElementMap infElt = infElt :=
  toElementMap_fixElement consMap

theorem relateNToC1_bot : relateNToC1.toElementMap NatDom.N.bot = C1.bot :=
  NatDom.constLiftN_bot C1 oneElem

theorem relateNToC1_natElem (n : ℕ) :
    relateNToC1.toElementMap (NatDom.natElem n) = oneElem n :=
  NatDom.constLiftN_natElem C1 oneElem n

end DomainTheory.NeighbourhoodSystems.UnarySeq
