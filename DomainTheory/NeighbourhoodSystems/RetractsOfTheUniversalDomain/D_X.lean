module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DiagFixed
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

/-- **The enumeration induced by the `qChar`-gated fold**: `D_X c` reads off the `V`-neighbourhood
presented at the fold's output raw index. -/
def D_X (c : ℕ) : Set α := P.X (myFoldCode P qChar cons c)
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

/-- **Theorem 8.8(c), Part 3 of 6, first half.** Every `D_X qChar cons c` is a `fixedNbhd
a`-neighbourhood — Part 2's invariant `diagFixed_myFoldCode`, repackaged via
`diagFixed_iff_fixedNbhd_mem`. -/
theorem D_X_mem {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c : ℕ) :
    (fixedNbhd a).mem (D_X P qChar cons c) :=
  (diagFixed_iff_fixedNbhd_mem P a _).mp (diagFixed_myFoldCode P qChar cons hqChar hcons c)

/-- **The reusable core of the surjectivity argument.** Any `V`-neighbourhood `P.X m` already
known to be `DiagFixed` (regardless of whether `m` itself is `myFoldCode`'s output) is `D_X qChar
cons c` for some list-code `c`: the singleton-list code witnessing `m` together with Part 1's
`qChar`-witness for it. -/
theorem D_X_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {m : ℕ} (hm : DiagFixed P a m) : ∃ c, D_X P qChar cons c = P.X m := by
  obtain ⟨i, hi⟩ := (hqChar m).mp hm
  refine ⟨encodeList [Nat.pair i m], ?_⟩
  have hstep : myFoldCode P qChar cons (encodeList [Nat.pair i m])
      = myStep P qChar cons P.masterIdx (Nat.pair i m) := by
    rw [myFoldCode_eq, decodeList_encodeList]
    unfold myFold
    rw [List.foldl_cons, List.foldl_nil]
  have hcond : cons (Nat.pair P.masterIdx m) = 1 := by
    apply (hcons P.masterIdx m).mpr
    refine ⟨m, ?_⟩
    have hsub : P.X m ⊆ V.master := V.sub_master (P.mem_X m)
    rw [P.masterIdx_spec]
    exact Set.subset_inter hsub subset_rfl
  have hstepval : myStep P qChar cons P.masterIdx (Nat.pair i m)
      = P.inter P.masterIdx m := by
    unfold myStep
    simp only [unpair_pair_snd]
    rw [(isOne_eq_one_iff _).mpr hi, (isOne_eq_one_iff _).mpr hcond, Nat.one_mul, selectFn_one]
  show D_X P qChar cons (encodeList [Nat.pair i m]) = P.X m
  unfold D_X
  rw [hstep, hstepval]
  have hcons' : (∃ k, P.X k ⊆ P.X P.masterIdx ∩ P.X m) := (hcons P.masterIdx m).mp hcond
  rw [P.inter_spec hcons', P.masterIdx_spec, Set.inter_eq_right.mpr (V.sub_master (P.mem_X m))]

/-- **Theorem 8.8(c), Part 3 of 6, second half.** Every `fixedNbhd a`-neighbourhood `Y` is
`D_X qChar cons c` for some list-code `c`: `P.surj` finds `Y`'s raw `V`-index, which is `DiagFixed`
since `Y` is `a`-fixed, and `D_X_of_diagFixed` finishes it. -/
theorem D_X_surj {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {Y : Set α} (hY : (fixedNbhd a).mem Y) : ∃ c, D_X P qChar cons c = Y := by
  obtain ⟨hYV, hYa⟩ := hY
  obtain ⟨n₀, hn₀⟩ := P.surj hYV
  have hdiag : DiagFixed P a n₀ := by unfold DiagFixed; rw [hn₀]; exact hYa
  obtain ⟨c, hc⟩ := D_X_of_diagFixed hqChar hcons hdiag
  exact ⟨c, by rw [hc, hn₀]⟩

/-- **The one genuine lemma of Theorem 8.8(c), Part 4 of 6.** `D`-consistency of two list-codes
(`∃ k, D_X k ⊆ D_X c₁ ∩ D_X c₂`) is equivalent to plain `V`-consistency of the underlying raw
`myFoldCode` indices. -/
theorem D_X_cons_iff {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c₁ c₂ : ℕ) :
    (∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) ↔
      (∃ k, P.X k ⊆ P.X (myFoldCode P qChar cons c₁) ∩ P.X (myFoldCode P qChar cons c₂)) := by
  set n₁ := myFoldCode P qChar cons c₁ with hn₁
  set n₂ := myFoldCode P qChar cons c₂ with hn₂
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨myFoldCode P qChar cons k, hk⟩
  · rintro ⟨k, hk⟩
    have hn1 : DiagFixed P a n₁ := diagFixed_myFoldCode P qChar cons hqChar hcons c₁
    have hn2 : DiagFixed P a n₂ := diagFixed_myFoldCode P qChar cons hqChar hcons c₂
    have hVmem : V.mem (P.X n₁ ∩ P.X n₂) := by
      rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
    have hfix : (fixedNbhd a).mem (P.X n₁ ∩ P.X n₂) :=
      (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a n₁).mp hn1)
        ((diagFixed_iff_fixedNbhd_mem P a n₂).mp hn2) hVmem
    have hm : DiagFixed P a (P.inter n₁ n₂) := by
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]; exact hfix
    obtain ⟨c, hc⟩ := D_X_of_diagFixed hqChar hcons hm
    have heq : D_X P qChar cons c = D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ := by
      rw [hc, P.inter_spec ⟨k, hk⟩]
      unfold D_X
      rw [← hn₁, ← hn₂]
    exact ⟨c, heq ▸ subset_rfl⟩

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

/-- **Theorem 8.8(c), Part 4 of 6, second half (`cons_computable`).** `D_X`-consistency is
`P.cons_computable` composed with the same primitive-recursive `myFoldCode`-pair reindex, via the
equivalence `D_X_cons_iff`. -/
theorem D_X_cons_computable {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    RecDecidable₂ (fun c₁ c₂ =>
      ∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) := by
  have hmf : Nat.Primrec (myFoldCode P qChar cons) := primrec_myFoldCode P qChar cons hqCharp hconsp
  have hreindex : Nat.Primrec (fun t : ℕ =>
      Nat.pair (myFoldCode P qChar cons t.unpair.1) (myFoldCode P qChar cons t.unpair.2)) :=
    (hmf.comp Nat.Primrec.left).pair (hmf.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) (P.cons_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact D_X_cons_iff hqChar hcons t.unpair.1 t.unpair.2

/-- **Theorem 8.8(c), Part 4 of 6, first half (`interEq_computable`, free).** `D_X c₁ ∩ D_X c₂ =
D_X c₃` is exactly `P.interEq_computable` reindexed along the primitive-recursive triple
`myFoldCode`. -/
theorem D_X_interEq_computable (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    RecDecidable₃ (fun c₁ c₂ c₃ =>
      D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ = D_X P qChar cons c₃) := by
  have hmf : Nat.Primrec (myFoldCode P qChar cons) := primrec_myFoldCode P qChar cons hqCharp hconsp
  have hreindex : Nat.Primrec (fun t : ℕ =>
      Nat.pair (myFoldCode P qChar cons t.unpair.1)
        (Nat.pair (myFoldCode P qChar cons t.unpair.2.unpair.1)
          (myFoldCode P qChar cons t.unpair.2.unpair.2))) :=
    (hmf.comp Nat.Primrec.left).pair
      ((hmf.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
        (hmf.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp hreindex)
  unfold D_X
  simp only [unpair_pair_fst, unpair_pair_snd]

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

/-- **The `.inter` field for `D_X`**: concatenate the two list-codes (`Recursive.lean`'s
Exercise 7.22 `appendListCode`), reusing that this is exactly `myFoldCode`'s left-fold-from-
`P.masterIdx` restarted at `myFoldCode c₁` (via `List.foldl_append`). -/
def D_inter (c₁ c₂ : ℕ) : ℕ := appendListCode c₁ c₂
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)
variable {P qChar cons}

theorem D_X_inter_eq (c₁ c₂ : ℕ) :
    D_X P qChar cons (D_inter c₁ c₂) =
      P.X ((decodeList c₂).foldl (myStep P qChar cons) (myFoldCode P qChar cons c₁)) := by
  have h1 : D_X P qChar cons (D_inter c₁ c₂) =
      P.X ((decodeList c₁ ++ decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    show P.X (myFoldCode P qChar cons (appendListCode c₁ c₂)) = _
    rw [myFoldCode_eq, appendListCode_eq]
    rfl
  have heq1 : (decodeList c₁).foldl (myStep P qChar cons) P.masterIdx =
      myFoldCode P qChar cons c₁ := (myFoldCode_eq P qChar cons c₁).symm
  rw [h1, List.foldl_append, heq1]
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

theorem D_inter_primrec : Nat.Primrec (fun t => D_inter t.unpair.1 t.unpair.2) :=
  primrec_appendListCode
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

/-- **One step of `myStep` only shrinks the presented set.** -/
theorem myStep_subset
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (r e : ℕ) :
    P.X (myStep P qChar cons r e) ⊆ P.X r := by
  unfold myStep
  have hq_dec : ((qChar e) ≠ 1) ∨ ((qChar e) = 1) := by
    by_cases hq : (qChar e) = 1
    · exact Or.inr hq
    · exact Or.inl hq
  rcases hq_dec with hq | hq
  · rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
  · rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair r e.unpair.2)) ≠ 1) ∨ ((cons (Nat.pair r e.unpair.2)) = 1) := by
      by_cases hc : (cons (Nat.pair r e.unpair.2)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero]
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, P.inter_spec ((hcons r e.unpair.2).mp hc)]
      exact Set.inter_subset_left

/-- **Folding only ever shrinks the presented set.** -/
theorem myFoldl_subset
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) :
    ∀ (l : List ℕ) (r : ℕ), P.X (l.foldl (myStep P qChar cons) r) ⊆ P.X r := by
  intro l
  induction l with
  | nil => intro r; simp only [List.foldl_nil]; exact subset_rfl
  | cons e rest ih =>
    intro r
    rw [List.foldl_cons]
    exact (ih (myStep P qChar cons r e)).trans (myStep_subset hcons r e)

/-- **The key lemma.** Refolding a list `l` from a start `n` that is `⊆` (in `P.X`) another start
`r`, reproduces `P.X n ∩ P.X (fold of l from r)` — *provided* this is already known to be
`V`-consistent at the end (i.e. `∃ k, P.X k ⊆ P.X n ∩ P.X (l.foldl … r)`). No `a`/`DiagFixed`
apparatus is needed: this is a purely structural fact about `myStep`'s consistency gate. -/
theorem myFoldl_inter_of_le
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) :
    ∀ (l : List ℕ) {n r : ℕ}, P.X n ⊆ P.X r →
      (∃ k, P.X k ⊆ P.X n ∩ P.X (l.foldl (myStep P qChar cons) r)) →
      P.X (l.foldl (myStep P qChar cons) n) = P.X n ∩ P.X (l.foldl (myStep P qChar cons) r) := by
  intro l
  induction l with
  | nil =>
    intro n r hnr _
    simp only [List.foldl_nil]
    exact (Set.inter_eq_left.mpr hnr).symm
  | cons e rest ih =>
    intro n r hnr hk
    simp only [List.foldl_cons] at hk ⊢
    have hq_dec : ((qChar e) ≠ 1) ∨ ((qChar e) = 1) := by
      by_cases hq : (qChar e) = 1
      · exact Or.inr hq
      · exact Or.inl hq
    rcases hq_dec with hq | hq
    · have hstepR : myStep P qChar cons r e = r := by
        unfold myStep; rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
      have hstepN : myStep P qChar cons n e = n := by
        unfold myStep; rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
      rw [hstepR] at hk ⊢
      rw [hstepN]
      exact ih hnr hk
    · have hc_dec : ((cons (Nat.pair r e.unpair.2)) ≠ 1) ∨ ((cons (Nat.pair r e.unpair.2)) = 1) := by
        by_cases hc : (cons (Nat.pair r e.unpair.2)) = 1
        · exact Or.inr hc
        · exact Or.inl hc
      rcases hc_dec with hc | hc
      · have hstepR : myStep P qChar cons r e = r := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, isOne_of_ne_one hc, selectFn_zero]
        have hcN : cons (Nat.pair n e.unpair.2) ≠ 1 := by
          intro hcn
          obtain ⟨w, hw⟩ := (hcons n e.unpair.2).mp hcn
          exact hc ((hcons r e.unpair.2).mpr
            ⟨w, hw.trans (Set.inter_subset_inter_left _ hnr)⟩)
        have hstepN : myStep P qChar cons n e = n := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, isOne_of_ne_one hcN, selectFn_zero]
        rw [hstepR] at hk ⊢
        rw [hstepN]
        exact ih hnr hk
      · obtain ⟨w0, hw0⟩ := (hcons r e.unpair.2).mp hc
        have hstepR : myStep P qChar cons r e = P.inter r e.unpair.2 := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, (isOne_eq_one_iff _).mpr hc, selectFn_one]
        rw [hstepR] at hk ⊢
        obtain ⟨k, hkk⟩ := hk
        have hYsub : P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2))
            ⊆ P.X e.unpair.2 := by
          refine (myFoldl_subset hcons rest (P.inter r e.unpair.2)).trans ?_
          rw [P.inter_spec ⟨w0, hw0⟩]
          exact Set.inter_subset_right
        have hkR : P.X k ⊆ P.X n := hkk.trans Set.inter_subset_left
        have hkY : P.X k ⊆ P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2)) :=
          hkk.trans Set.inter_subset_right
        have hkne : P.X k ⊆ P.X e.unpair.2 := hkY.trans hYsub
        have hwitN : ∃ k, P.X k ⊆ P.X n ∩ P.X e.unpair.2 := ⟨k, Set.subset_inter hkR hkne⟩
        have hcN : cons (Nat.pair n e.unpair.2) = 1 := (hcons n e.unpair.2).mpr hwitN
        have hstepN : myStep P qChar cons n e = P.inter n e.unpair.2 := by
          unfold myStep
          rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul, (isOne_eq_one_iff _).mpr hcN, selectFn_one]
        rw [hstepN]
        have hnr' : P.X (P.inter n e.unpair.2) ⊆ P.X (P.inter r e.unpair.2) := by
          rw [P.inter_spec hwitN, P.inter_spec ⟨w0, hw0⟩]
          exact Set.inter_subset_inter_left _ hnr
        have hk' : ∃ k', P.X k' ⊆ P.X (P.inter n e.unpair.2) ∩
            P.X (rest.foldl (myStep P qChar cons) (P.inter r e.unpair.2)) := by
          refine ⟨k, ?_⟩
          rw [P.inter_spec hwitN]
          exact Set.subset_inter (Set.subset_inter hkR hkne) hkY
        rw [ih hnr' hk', P.inter_spec hwitN, Set.inter_assoc, Set.inter_eq_right.mpr hYsub]

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)
variable {P qChar cons}

/-- **Theorem 8.8(c), Part 5 of 6, headline.** Given `D`-consistency of `c₁`, `c₂`,
`D_X (D_inter c₁ c₂) = D_X c₁ ∩ D_X c₂`. The hypothesis is already stated at the `V`-side (`D_X`'s
codomain *is* `P.X` of a raw index), so `myFoldl_inter_of_le` applies directly with `n :=
myFoldCode c₁`, `r := P.masterIdx`. -/
theorem D_X_inter_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) {c₁ c₂ : ℕ}
    (h : ∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) :
    D_X P qChar cons (D_inter c₁ c₂) = D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ := by
  have heq2 : D_X P qChar cons c₂ =
      P.X ((decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    show P.X (myFoldCode P qChar cons c₂) = _
    rw [myFoldCode_eq]
    rfl
  have hnr : P.X (myFoldCode P qChar cons c₁) ⊆ P.X P.masterIdx := by
    rw [P.masterIdx_spec]
    exact V.sub_master (P.mem_X _)
  have hk : ∃ k, P.X k ⊆ P.X (myFoldCode P qChar cons c₁) ∩
      P.X ((decodeList c₂).foldl (myStep P qChar cons) P.masterIdx) := by
    obtain ⟨k, hk0⟩ := h
    refine ⟨myFoldCode P qChar cons k, ?_⟩
    rw [← heq2]
    exact hk0
  rw [D_X_inter_eq, myFoldl_inter_of_le hcons (decodeList c₂) hnr hk, ← heq2]
  rfl
end

end DomainTheory.NeighbourhoodSystems
