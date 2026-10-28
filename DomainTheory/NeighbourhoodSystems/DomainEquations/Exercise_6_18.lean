module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_17

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem_6_14

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510
namespace Exercise618
variable {α : Type*} {V : NeighborhoodSystem α}

def iterIsInitial (Dom : StrictDomainObj.{w}) : IsInitial (iterAlg Dom) where
  desc := descAlgHom Dom
  uniq B h := by
    obtain ⟨hom, comm⟩ := h
    have hcomm : hom.1.comp (imap Dom.sys)
        = B.str.1.comp (prodMap (idMap Dom.sys) hom.1) := congrArg Subtype.val comm
    have hg : hom.1 = descMap B.str.1 :=
      comm_unique B.str.1 hom.2 (descMap_strict B.str.1 B.str.2) hcomm (descMap_comm B.str.1)
    have hhom : hom = ⟨descMap B.str.1, descMap_strict B.str.1 B.str.2⟩ := Subtype.ext hg
    subst hhom
    rfl

end Exercise618
end

section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

def toS (z : (Dsharp D hD).Element) : (sumSys D hD).Element where
  mem W := W = sumMaster D (prod (Dsharp D hD) (Dsharp D hD))
    ∨ (∃ X, D.mem X ∧ W = inj₀ X ∧ z.mem (embZero X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = inj₁ (prodNbhd P Q) ∧ z.mem (embPair P Q))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨prodNbhd P Q, prod_mem_prodNbhd hP hQ, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨P', Q', hP', hQ', rfl, hzPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [sumMaster_inter_inj₁ (prod_mem_prodNbhd hP' hQ')], hzPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embZero_inter] at hz
        exact memS_embZero_inv hD (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embZero_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzPQ'; rw [embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (prod_mem_prodNbhd hP hQ)], hzPQ⟩)
    · exfalso
      have hz := z.inter_mem hzPQ hzX'; rw [Set.inter_comm, embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [inj₁_inter, prodNbhd_inter], ?_⟩)
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).1
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).2
      · have hz := z.inter_mem hzPQ hzPQ'; rwa [embPair_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩) hW' hsub
    · left
      exact eq_sumMaster_of_subset hW' hsub
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemS.zero hX') (embZero_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · obtain ⟨a, ha⟩ := hD X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD (prodNbhd P Q) (prod_mem_prodNbhd hP hQ)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨P', Q', hP', hQ', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := prodNbhd_subset_iff.mp (inj₁_subset_inj₁.mp hsub)
        exact z.up_mem hzPQ (MemS.pair hP' hQ') (embPair_subset.mpr ⟨hPP, hQQ⟩)

@[simp] theorem toS_mem_inj₀ {z : (Dsharp D hD).Element} {X : Set α} (hX : D.mem X) :
    (toS D hD z).mem (inj₀ X) ↔ z.mem (embZero X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P, Q, hP, hQ, heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₀
    · rwa [inj₀_injective heq]
    · obtain ⟨a, ha⟩ := hD X hX
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
  · intro hz; exact Or.inr (Or.inl ⟨X, hX, rfl, hz⟩)

@[simp] theorem toS_mem_inj₁ {z : (Dsharp D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (toS D hD z).mem (inj₁ (prodNbhd P Q)) ↔ z.mem (embPair P Q) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hz⟩ | ⟨P', Q', hP', hQ', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_sumMaster) none_mem_inj₁
    · obtain ⟨a, ha⟩ := hD X' hX'
      exact absurd (heq ▸ il_mem_inj₀.mpr ha) il_mem_inj₁
    · obtain ⟨hPP, hQQ⟩ := prodNbhd_injective (inj₁_injective heq)
      rw [hPP, hQQ]; exact hz
  · intro hz; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hz⟩)

theorem embPair_ne_Gamma (P Q : Set (List Bool × α)) : embPair P Q ≠ Gamma D := by
  intro h
  obtain ⟨a, ha⟩ := hD D.master D.master_mem
  have hmem : (([], a) : List Bool × α) ∈ Gamma D := ha
  rw [← h] at hmem
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

theorem embZero_ne_Gamma (X : Set α) : embZero X ≠ Gamma D := by
  intro h
  obtain ⟨a, ha⟩ := hD D.master D.master_mem
  have hmem : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
  rw [← h] at hmem; exact absurd hmem.1 (by simp)

theorem embZero_ne_embPair {X : Set α} (hX : D.mem X) (P Q : Set (List Bool × α)) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨a, ha⟩ := hD X hX
  have hmem : (([], a) : List Bool × α) ∈ embPair P Q := h ▸ (⟨rfl, ha⟩ : ([], a) ∈ embZero X)
  rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · simp at hp'
  · simp at hq'

def fromS (s : (sumSys D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D
    ∨ (∃ X, D.mem X ∧ W = embZero X ∧ s.mem (inj₀ X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = embPair P Q ∧ s.mem (inj₁ (prodNbhd P Q)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact MemS.gamma
    · exact MemS.zero hX
    · exact MemS.pair hP hQ
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨P', Q', hP', hQ', rfl, hsPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX',
        by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma hX')], hsX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [Set.inter_eq_right.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP') (memS_subset_gamma hQ'))], hsPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hX)], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embZero_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv D hD (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsPQ'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_eq_left.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))], hsPQ⟩)
    · exfalso
      have hs := s.inter_mem hsPQ hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [embPair_inter], ?_⟩)
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).1
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).2
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embZero_subset.mp hsub))
      | @pair P' Q' hP' hQ' =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        have hmem : (([], a) : List Bool × α) ∈ embPair P' Q' := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        have hz : t ∈ embZero X' := hsub ht
        exact hcons hz.1
      | @pair P' Q' hP' hQ' =>
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact s.up_mem hsPQ (Or.inr (Or.inr ⟨prodNbhd P' Q', prod_mem_prodNbhd hP' hQ', rfl⟩))
          (inj₁_subset_inj₁.mpr (prodNbhd_subset_iff.mpr ⟨hPP, hQQ⟩))

@[simp] theorem fromS_mem_embZero {s : (sumSys D hD).Element} {X : Set α} (hX : D.mem X) :
    (fromS D hD s).mem (embZero X) ↔ s.mem (inj₀ X) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P, Q, hP, hQ, heq, hs⟩)
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rwa [embZero_injective heq]
    · exact absurd heq (embZero_ne_embPair D hD hX P Q)
  · intro hs; exact Or.inr (Or.inl ⟨X, hX, rfl, hs⟩)

@[simp] theorem fromS_mem_embPair {s : (sumSys D hD).Element} {P Q : Set (List Bool × α)}
    (hP : MemS D P) (hQ : MemS D Q) :
    (fromS D hD s).mem (embPair P Q) ↔ s.mem (inj₁ (prodNbhd P Q)) := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hs⟩ | ⟨P', Q', hP', hQ', heq, hs⟩)
    · exact absurd h0 (embPair_ne_Gamma D hD P Q)
    · exact absurd heq.symm (embZero_ne_embPair D hD hX' P Q)
    · obtain ⟨hPP, hQQ⟩ := embPair_injective heq
      rw [hPP, hQQ]; exact hs
  · intro hs; exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hs⟩)

theorem fromS_toS (z : (Dsharp D hD).Element) : fromS D hD (toS D hD z) = z := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact z.master_mem
    · exact (toS_mem_inj₀ D hD hX).mp hs
    · exact (toS_mem_inj₁ D hD hP hQ).mp hs
  · intro hW
    cases z.sub hW with
    | gamma => exact Or.inl rfl
    | @zero X hX => exact Or.inr (Or.inl ⟨X, hX, rfl, (toS_mem_inj₀ D hD hX).mpr hW⟩)
    | @pair P Q hP hQ => exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (toS_mem_inj₁ D hD hP hQ).mpr hW⟩)

def inSharp (x : D.Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ X, x.mem X ∧ W = embZero X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl⟩)
    · exact MemS.gamma
    · exact MemS.zero (x.sub hX)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) (rfl | ⟨X', hX', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma (x.sub hX'))]⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma (x.sub hX))]⟩
    · exact Or.inr ⟨X ∩ X', x.inter_mem hX hX', by rw [embZero_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' => exact Or.inr ⟨X', x.up_mem hX hX' (embZero_subset.mp hsub), rfl⟩
      | @pair P Q hP hQ =>
        exfalso
        obtain ⟨a, ha⟩ := hD X (x.sub hX)
        have hmem : (([], a) : List Bool × α) ∈ embPair P Q := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'

def pairSharp (x y : (Dsharp D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D ∨ ∃ P Q, x.mem P ∧ y.mem Q ∧ W = embPair P Q
  sub := by
    rintro W (rfl | ⟨P, Q, hP, hQ, rfl⟩)
    · exact MemS.gamma
    · exact MemS.pair (x.sub hP) (y.sub hQ)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) (rfl | ⟨P', Q', hP', hQ', rfl⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨P', Q', hP', hQ', by
        rw [Set.inter_eq_right.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP'))
          (memS_subset_gamma (y.sub hQ')))]⟩
    · exact Or.inr ⟨P, Q, hP, hQ, by
        rw [Set.inter_eq_left.mpr (embPair_subset_Gamma (memS_subset_gamma (x.sub hP))
          (memS_subset_gamma (y.sub hQ)))]⟩
    · exact Or.inr ⟨P ∩ P', Q ∩ Q', x.inter_mem hP hP', y.inter_mem hQ hQ', by rw [embPair_inter]⟩
  up_mem := by
    rintro W W' (rfl | ⟨P, Q, hP, hQ, rfl⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD (x.sub hP)) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        exact hcons (hsub ht).1
      | @pair P' Q' hP' hQ' =>
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact Or.inr ⟨P', Q', x.up_mem hP hP' hPP, y.up_mem hQ hQ' hQQ, rfl⟩

theorem toS_fromS (s : (sumSys D hD).Element) : toS D hD (fromS D hD s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨P, Q, hP, hQ, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromS_mem_embZero D hD hX).mp hs
    · exact (fromS_mem_embPair D hD hP hQ).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨V, hV, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromS_mem_embZero D hD hX).mpr hW⟩)
    · obtain ⟨P, Q, hP, hQ, rfl⟩ := hV
      exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, (fromS_mem_embPair D hD hP hQ).mpr hW⟩)

def dsharpEquiv : (Dsharp D hD).Element ≃o (sumSys D hD).Element where
  toFun := toS D hD
  invFun := fromS D hD
  left_inv := fromS_toS D hD
  right_inv := toS_fromS D hD
  map_rel_iff' := by
    intro z z'
    constructor
    · intro h X hX
      cases z.sub hX with
      | gamma => exact z'.master_mem
      | @zero A hA =>
        exact (toS_mem_inj₀ D hD hA).mp (h _ (Or.inr (Or.inl ⟨A, hA, rfl, hX⟩)))
      | @pair P Q hP hQ =>
        exact (toS_mem_inj₁ D hD hP hQ).mp (h _ (Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, hX⟩)))
    · intro h W hW
      rcases hW with rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, hX, rfl, h _ hzX⟩)
      · exact Or.inr (Or.inr ⟨P, Q, hP, hQ, rfl, h _ hzPQ⟩)

theorem dsharp_domain_equation :
    Dsharp D hD ≅ᴰ sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD) :=
  ⟨dsharpEquiv D hD⟩

theorem inSharp_le_iff {x x' : D.Element} : inSharp D hD x ≤ inSharp D hD x' ↔ x ≤ x' := by
  constructor
  · intro h X hX
    rcases h (embZero X) (Or.inr ⟨X, hX, rfl⟩) with h0 | ⟨X', hX', heq⟩
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rw [← embZero_injective heq] at hX'; exact hX'
  · intro h W hW
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h _ hX, rfl⟩

theorem pairSharp_le_iff {x x' y y' : (Dsharp D hD).Element} :
    pairSharp D hD x y ≤ pairSharp D hD x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
    · rcases h (embPair P (Gamma D)) (Or.inr ⟨P, Gamma D, hP, y.master_mem, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD P (Gamma D))
      · obtain ⟨hPP, -⟩ := embPair_injective heq; rw [← hPP] at hP'; exact hP'
    · rcases h (embPair (Gamma D) Q) (Or.inr ⟨Gamma D, Q, x.master_mem, hQ, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD (Gamma D) Q)
      · obtain ⟨-, hQQ⟩ := embPair_injective heq; rw [← hQQ] at hQ'; exact hQ'
  · rintro ⟨hx, hy⟩ W hW
    rcases hW with rfl | ⟨P, Q, hP, hQ, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨P, Q, hx _ hP, hy _ hQ, rfl⟩

end Equation

end Example61
end

end DomainTheory.NeighbourhoodSystems
end
