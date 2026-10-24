module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_25

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
section
open NeighborhoodSystem
variable {α : Type*}

/- concordance: source L4943 THEOREM 8.8 universality of U -/
/-- **First sentence of Theorem 8.8 (Scott 1981, PRG-19, Lecture VIII).** `𝒰` is universal: every *countable*
neighbourhood system `D` embeds, up to isomorphism, as a subsystem of `𝒰`.

The enumeration `e` is built from any surjection `f : ℕ → {S // D.mem S}` (`exists_surjective_nat`,
using `Countable`/`Nonempty` — the only place `Classical.choice` enters, since neither hypothesis is
data), shifted by one and patched at `0` to enforce Scott's convention `X₀ = Δ`. Everything else —
`idxSet`'s "separated" reindexing, the `Yidx`/transfer apparatus of `Theorem88.lean`, and the
`DprimeU`/`domainIso` machinery above — is then assembled directly. -/
theorem theorem_8_8_a.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] :
    ∃ D' : NeighborhoodSystem ℚ, (D ≅ᴰ D') ∧ (D' ◁ U) := by
  have : Nonempty {S : Set α // D.mem S} := ⟨⟨D.master, D.master_mem⟩⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat {S : Set α // D.mem S}
  set e : ℕ → Set α := fun n => if n = 0 then D.master else (f (n - 1)).1 with hedef
  have he0 : e 0 = D.master := ite_eq_left rfl
  have hen : ∀ n, e (n + 1) = (f n).1 := by
    intro n
    show (if n + 1 = 0 then D.master else (f (n + 1 - 1)).1) = (f n).1
    rw [ite_eq_right (Nat.succ_ne_zero n), Nat.succ_sub_one]
  have hcover : ∀ S, D.mem S ↔ ∃ n, S = e n := by
    intro S
    constructor
    · intro hS
      obtain ⟨k, hk⟩ := hf ⟨S, hS⟩
      exact ⟨k + 1, by rw [hen k]; exact (congrArg Subtype.val hk).symm⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => rw [he0]; exact D.master_mem
      | succ n => rw [hen n]; exact (f n).2
  exact ⟨DprimeU D e hcover he0, isomorphic_DprimeU D e hcover he0, DprimeU_subsystem D e hcover he0⟩

/-- **First sentence of Theorem 8.8 (Scott 1981, PRG-19).** Scott's wording:
"The system `𝒰` is universal in the sense that, for every countable neighbourhood
system `𝒟`, we have `𝒟 ⊴ 𝒰`." This packages `theorem_8_8_a` as that relation. -/
theorem theorem_8_8.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] : D ⊴ U := by
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The `idxSet`-atom of the *positive* constraints `pos`: indices `m` with `Xₘ ⊆ Xᵢ` for every
`i ∈ pos`. (The empty list gives `Set.univ`, matching `genAtom`'s depth-`0` value.) -/
def IPos (pos : List ℕ) : Set ℕ := {m | ∀ i ∈ pos, m ∈ idxSet P.X i}

@[simp] theorem IPos_nil : IPos P [] = Set.univ := by
  ext m; simp [IPos]

/-- **The full atom**: positive constraints `pos` together with negative constraints `neg`
(`¬(Xₘ ⊆ Xⱼ)` for `j ∈ neg`). This is `genAtom (idxSet P.X) Set.univ δ n` for the sign sequence
built from `pos`/`neg`. -/
def DAtom (pos neg : List ℕ) : Set ℕ := IPos P pos ∩ {m | ∀ j ∈ neg, m ∉ idxSet P.X j}

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

/-- One step of the positive meet-fold. The accumulator `r` codes `(ok, idx)`
(`r.unpair.1 = ok`, `r.unpair.2 = idx`); `i` is the next positive-constraint index. If the fold is
still "ok" and `P`'s consistency decider accepts `(idx, i)`, advance to `P.inter idx i`; otherwise
the fold is permanently "not ok" (accumulator frozen at the last good `idx`, which is discarded by
`meetFold_spec` in that case anyway). -/
def meetStep (r i : ℕ) : ℕ :=
  selectFn (isOne r.unpair.1 * isOne (cons (Nat.pair r.unpair.2 i)))
    (Nat.pair 1 (P.inter r.unpair.2 i)) (Nat.pair 0 r.unpair.2)

/-- **The positive meet-fold**: fold `meetStep` across `pos`, starting from `(ok, idx) = (1,
masterIdx)` (the empty meet is `Δ`, always "ok"). -/
def meetFold (l : List ℕ) : ℕ := l.foldl (meetStep P cons) (Nat.pair 1 P.masterIdx)

@[simp] theorem meetFold_nil : meetFold P cons [] = Nat.pair 1 P.masterIdx := rfl

/-- `foldCode`-shaped step matching `meetStep`: state `w = pair i (pair r params)` (`params`
unused). -/
def meetStepCode (w : ℕ) : ℕ := meetStep P cons w.unpair.2.unpair.1 w.unpair.1

/-- The code-level positive meet-fold. -/
def meetFoldCode (c : ℕ) : ℕ := foldCode (meetStepCode P cons) 0 (Nat.pair 1 P.masterIdx) c

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)
variable (incl : ℕ → ℕ)

/-- **The full `DAtom`-emptiness decider.** `1` iff `DAtom (decodeList posC) (decodeList negC) =
∅`: either the positive meet is already inconsistent (`ok ≠ 1`), or the meet's index `idx` lies
inside some negative target (bounded existential over `decodeList negC`, via `existsListChar`). -/
def DAtomEmptyChar (posC negC : ℕ) : ℕ :=
  selectFn (isOne (meetFoldCode P cons posC).unpair.1)
    (existsListChar (fun t => incl (Nat.pair t.unpair.2 t.unpair.1))
      (meetFoldCode P cons posC).unpair.2 negC)
    1
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem IPos_cons (i : ℕ) (rest : List ℕ) :
    IPos P (i :: rest) = idxSet P.X i ∩ IPos P rest := by
  ext m
  simp only [IPos, Set.mem_ofPred_eq, List.mem_cons, mem_idxSet, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨h i (Or.inl rfl), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨hi, hrest⟩ j (rfl | hj)
    · exact hi
    · exact hrest j hj

/-- `idxSet P.X P.masterIdx = Set.univ`: `masterIdx` indexes `D`'s master `Δ`, and every
`D`-neighbourhood is `⊆ Δ`. -/
theorem idxSet_masterIdx_eq_univ : idxSet P.X P.masterIdx = Set.univ :=
  Set.eq_univ_of_forall fun m => by
    show P.X m ⊆ P.X P.masterIdx
    rw [P.masterIdx_spec]
    exact D.sub_master (P.mem_X m)

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

theorem meetFoldCode_eq (c : ℕ) : meetFoldCode P cons c = meetFold P cons (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => meetStepCode P cons (Nat.pair x (Nat.pair acc 0)))
      = meetStep P cons := by
    funext acc x
    unfold meetStepCode
    simp only [unpair_pair_fst, unpair_pair_snd]
  unfold meetFoldCode meetFold
  rw [foldCode_eq', hfun]

theorem meetFold_cons (i : ℕ) (rest : List ℕ) :
    meetFold P cons (i :: rest) = (rest.foldl (meetStep P cons) (meetStep P cons
      (Nat.pair 1 P.masterIdx) i)) := by
  unfold meetFold; rw [List.foldl_cons]

theorem meetStep_ok_le_one (r i : ℕ) : (meetStep P cons r i).unpair.1 ≤ 1 := by
  have h1 := isOne_le_one r.unpair.1
  have h2 := isOne_le_one (cons (Nat.pair r.unpair.2 i))
  unfold meetStep
  rcases (show isOne r.unpair.1 = 0 ∨ isOne r.unpair.1 = 1 by omega) with h | h
  · rw [h, Nat.zero_mul, selectFn_zero, unpair_pair_fst]; exact Nat.zero_le 1
  · rw [h, Nat.one_mul]
    rcases (show isOne (cons (Nat.pair r.unpair.2 i)) = 0 ∨
        isOne (cons (Nat.pair r.unpair.2 i)) = 1 by omega) with h' | h'
    · rw [h', selectFn_zero, unpair_pair_fst]; exact Nat.zero_le 1
    · rw [h', selectFn_one, unpair_pair_fst]

/-- **One-step transfer of the meet-fold invariant**: if `init` codes `(ok, idx)` faithfully
relative to some set `S` (`ok = 1 → idxSet idx = S`, `ok = 0 → S = ∅`), then `meetStep init i`
codes the same relative to `S ∩ idxSet i` — the positive constraint contributed by `i`. -/
theorem meetStep_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {init : ℕ} {S : Set ℕ} (hle : init.unpair.1 ≤ 1)
    (h1 : init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S)
    (h0 : init.unpair.1 = 0 → S = ∅) (i : ℕ) :
    (meetStep P cons init i).unpair.1 ≤ 1 ∧
      ((meetStep P cons init i).unpair.1 = 1 →
        idxSet P.X (meetStep P cons init i).unpair.2 = S ∩ idxSet P.X i) ∧
      ((meetStep P cons init i).unpair.1 = 0 → S ∩ idxSet P.X i = ∅) := by
  refine ⟨meetStep_ok_le_one P cons init i, ?_, ?_⟩ <;>
    (unfold meetStep
     rcases (show init.unpair.1 = 0 ∨ init.unpair.1 = 1 by omega) with hi | hi)
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro h; exact absurd h (by decide)
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro h; exact absurd h (by decide)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_snd, unpair_pair_fst]
      intro _
      have heq : P.X init.unpair.2 ∩ P.X i = P.X (P.inter init.unpair.2 i) :=
        (P.inter_spec (hcons _ _ |>.mp hc)).symm
      rw [← idxSet_inter_of_inter_eq (e := P.X) heq, h1 hi]
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro _
    rw [h0 hi]; simp
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro _
      rw [← h1 hi]
      ext m
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hm1 hm2
      exact hc ((hcons _ _).mpr ⟨m, Set.subset_inter hm1 hm2⟩)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_fst]
      intro h; exact absurd h (by decide)

/-- **The meet-fold invariant, folded across a whole list.** Generalizes `meetStep_spec` from one
step to a full list `l`, relative to an arbitrary starting accumulator `init`/set `S`. -/
theorem meetFold_foldl_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {init : ℕ} {S : Set ℕ}, init.unpair.1 ≤ 1 →
      (init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S) → (init.unpair.1 = 0 → S = ∅) →
      (l.foldl (meetStep P cons) init).unpair.1 ≤ 1 ∧
        ((l.foldl (meetStep P cons) init).unpair.1 = 1 →
          idxSet P.X (l.foldl (meetStep P cons) init).unpair.2 = S ∩ IPos P l) ∧
        ((l.foldl (meetStep P cons) init).unpair.1 = 0 → S ∩ IPos P l = ∅) := by
  induction l with
  | nil =>
    intro init S hle h1 h0
    simpa using ⟨hle, h1, h0⟩
  | cons i rest ih =>
    intro init S hle h1 h0
    rw [List.foldl_cons, IPos_cons, ← Set.inter_assoc]
    obtain ⟨hle', h1', h0'⟩ := meetStep_spec P cons hcons hle h1 h0 i
    exact ih hle' h1' h0'

/-- **Correctness of the positive meet-fold**, instantiated at the real starting point
`(1, masterIdx)`/`Set.univ`. -/
theorem meetFold_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (pos : List ℕ) :
    (meetFold P cons pos).unpair.1 ≤ 1 ∧
      ((meetFold P cons pos).unpair.1 = 1 →
        idxSet P.X (meetFold P cons pos).unpair.2 = IPos P pos) ∧
      ((meetFold P cons pos).unpair.1 = 0 → IPos P pos = ∅) := by
  have hinit1 : (Nat.pair 1 P.masterIdx).unpair.1 = 1 := unpair_pair_fst 1 P.masterIdx
  have hinit2 : (Nat.pair 1 P.masterIdx).unpair.2 = P.masterIdx := unpair_pair_snd 1 P.masterIdx
  have h := meetFold_foldl_spec P cons hcons pos (init := Nat.pair 1 P.masterIdx) (S := Set.univ)
    (by rw [hinit1]) (fun _ => by rw [hinit2]; exact idxSet_masterIdx_eq_univ P)
    (fun h => absurd (hinit1.symm.trans h) (by norm_num))
  simpa only [meetFold, Set.univ_inter] using h

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem mem_IPos {pos : List ℕ} {m : ℕ} : m ∈ IPos P pos ↔ ∀ i ∈ pos, P.X m ⊆ P.X i := Iff.rfl

theorem mem_DAtom {pos neg : List ℕ} {m : ℕ} :
    m ∈ DAtom P pos neg ↔ (∀ i ∈ pos, P.X m ⊆ P.X i) ∧ (∀ j ∈ neg, ¬ P.X m ⊆ P.X j) := by
  simp only [DAtom, Set.mem_inter_iff, mem_IPos, Set.mem_ofPred_eq, mem_idxSet]

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

/-- **The core emptiness characterization.** `DAtom pos neg` is empty iff either the positive
part is inconsistent, or the meet's own index `idx` already lies inside some negative target
`Xⱼ` (forcing every candidate below it there too). -/
theorem DAtom_eq_empty_iff
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (pos neg : List ℕ) :
    DAtom P pos neg = ∅ ↔
      (meetFold P cons pos).unpair.1 ≠ 1 ∨
        ∃ j ∈ neg, P.X (meetFold P cons pos).unpair.2 ⊆ P.X j := by
  obtain ⟨hle, h1, h0⟩ := meetFold_spec P cons hcons pos
  set r := meetFold P cons pos with hrdef
  rcases (show r.unpair.1 = 0 ∨ r.unpair.1 = 1 by omega) with hr | hr
  · have hIPos : IPos P pos = ∅ := h0 hr
    simp only [hr, ne_eq, zero_ne_one, not_false_eq_true, true_or, iff_true]
    ext m
    simp only [DAtom, hIPos, Set.mem_inter_iff, Set.mem_empty_iff_false, false_and,
      Set.mem_empty_iff_false]
  · have hIPos : idxSet P.X r.unpair.2 = IPos P pos := h1 hr
    simp only [hr, ne_eq, not_true_eq_false, false_or]
    constructor
    · intro hempty
      by_contra hcon
      push Not at hcon
      have hmem : r.unpair.2 ∈ DAtom P pos neg := by
        rw [mem_DAtom]
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have hself : r.unpair.2 ∈ IPos P pos := hIPos ▸ self_mem_idxSet P.X r.unpair.2
          exact hself i hi
        · exact hcon j hj
      rw [hempty] at hmem
      exact absurd hmem (Set.notMem_empty _)
    · rintro ⟨j, hj, hsub⟩
      ext m
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hmem
      rw [mem_DAtom] at hmem
      have hmsub : P.X m ⊆ P.X r.unpair.2 := by
        have hmI : m ∈ IPos P pos := hmem.1
        rw [← hIPos] at hmI
        exact hmI
      exact hmem.2 j hj (hmsub.trans hsub)
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)
variable (incl : ℕ → ℕ)

theorem DAtomEmptyChar_eq_one_iff
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    (hincl : ∀ n m, incl (Nat.pair n m) = 1 ↔ P.X n ⊆ P.X m) (posC negC : ℕ) :
    DAtomEmptyChar P cons incl posC negC = 1 ↔
      DAtom P (decodeList posC) (decodeList negC) = ∅ := by
  rw [DAtom_eq_empty_iff P cons hcons, ← meetFoldCode_eq]
  set r := meetFoldCode P cons posC with hrdef
  unfold DAtomEmptyChar
  by_cases hok : r.unpair.1 = 1
  · rw [(isOne_eq_one_iff _).mpr hok, selectFn_one, existsListChar_eq_one_iff]
    simp only [ne_eq, hok, not_true_eq_false, false_or]
    constructor
    · rintro ⟨j, hj, hgj⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hgj
      exact ⟨j, hj, (hincl _ _).mp hgj⟩
    · rintro ⟨j, hj, hsub⟩
      refine ⟨j, hj, ?_⟩
      simp only [unpair_pair_fst, unpair_pair_snd]
      exact (hincl _ _).mpr hsub
  · rw [isOne_of_ne_one hok, selectFn_zero]
    simp only [ne_eq, hok, not_false_eq_true, true_or]
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)

theorem primrec_meetStepCode (hconsp : Nat.Primrec cons) : Nat.Primrec (meetStepCode P cons) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hrok : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) := Nat.Primrec.left.comp hr
  have hridx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp hr
  have hconstest : Nat.Primrec (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1.unpair.2 w.unpair.1)) :=
    hconsp.comp (hridx.pair hx)
  have hcond : Nat.Primrec
      (fun w : ℕ => isOne w.unpair.2.unpair.1.unpair.1 * isOne
        (cons (Nat.pair w.unpair.2.unpair.1.unpair.2 w.unpair.1))) :=
    primrec_mul₂ (primrec_isOne.comp hrok) (primrec_isOne.comp hconstest)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1.unpair.2 w.unpair.1) :=
    (P.inter_primrec.comp (hridx.pair hx)).of_eq
      (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hthen : Nat.Primrec
      (fun w : ℕ => Nat.pair 1 (P.inter w.unpair.2.unpair.1.unpair.2 w.unpair.1)) :=
    (Nat.Primrec.const 1).pair hinter
  have helse : Nat.Primrec (fun w : ℕ => Nat.pair 0 w.unpair.2.unpair.1.unpair.2) :=
    (Nat.Primrec.const 0).pair hridx
  exact (primrec_selectFn hcond hthen helse).of_eq (fun _ => rfl)

theorem primrec_meetFoldCode (hconsp : Nat.Primrec cons) :
    Nat.Primrec (meetFoldCode P cons) :=
  (primrec_foldCode (primrec_meetStepCode P cons hconsp) (Nat.Primrec.const 0)
    (Nat.Primrec.const (Nat.pair 1 P.masterIdx)) primrec_id).of_eq (fun _ => rfl)

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable (cons : ℕ → ℕ)
variable (incl : ℕ → ℕ)

theorem primrec_DAtomEmptyChar (hconsp : Nat.Primrec cons) (hinclp : Nat.Primrec incl) :
    Nat.Primrec (fun t => DAtomEmptyChar P cons incl t.unpair.1 t.unpair.2) := by
  have hmf : Nat.Primrec (fun t : ℕ => meetFoldCode P cons t.unpair.1) :=
    (primrec_meetFoldCode P cons hconsp).comp Nat.Primrec.left
  have hmfok : Nat.Primrec (fun t : ℕ => (meetFoldCode P cons t.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hmf
  have hmfidx : Nat.Primrec (fun t : ℕ => (meetFoldCode P cons t.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hmf
  have hg : Nat.Primrec (fun s : ℕ => incl (Nat.pair s.unpair.2 s.unpair.1)) :=
    hinclp.comp (Nat.Primrec.right.pair Nat.Primrec.left)
  have hexists : Nat.Primrec
      (fun t : ℕ => existsListChar (fun s => incl (Nat.pair s.unpair.2 s.unpair.1))
        (meetFoldCode P cons t.unpair.1).unpair.2 t.unpair.2) := by
    have hcomb : Nat.Primrec (fun t : ℕ =>
        Nat.pair t.unpair.2 (meetFoldCode P cons t.unpair.1).unpair.2) :=
      Nat.Primrec.right.pair hmfidx
    exact ((primrec_existsListChar hg).comp hcomb).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  exact (primrec_selectFn (primrec_isOne.comp hmfok) hexists (Nat.Primrec.const 1)).of_eq
    (fun _ => rfl)

/-- **Part 5's headline result.** `D`-side atom emptiness (in the `idxSet` sense above) is
recursively decidable in the two constraint-list codes, for any `ComputablePresentation` of `D`.
The primitive-recursive deciders `cons`/`incl` are extracted from `P.cons_computable`/
`P.incl_computable` *inside* this `Prop`-valued goal — an ordinary `Exists`-elimination into a
`Prop`, so this needs no `Classical.choice` beyond what `P` itself already carries. -/
theorem DAtom_recDecidable :
    RecDecidable₂ (fun posC negC => DAtom P (decodeList posC) (decodeList negC) = ∅) := by
  obtain ⟨cons, hconsp, hconss⟩ := P.cons_computable
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have := hconss (Nat.pair n m)
    simpa only [unpair_pair_fst, unpair_pair_snd] using this.symm
  have hincl : ∀ n m, incl (Nat.pair n m) = 1 ↔ P.X n ⊆ P.X m := by
    intro n m
    have := hincls (Nat.pair n m)
    simpa only [unpair_pair_fst, unpair_pair_snd] using this.symm
  refine ⟨fun t => DAtomEmptyChar P cons incl t.unpair.1 t.unpair.2,
    primrec_DAtomEmptyChar P cons incl hconsp hinclp, fun t => ?_⟩
  exact (DAtomEmptyChar_eq_one_iff P cons incl hcons hincl t.unpair.1 t.unpair.2).symm

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 8.8(c), Part 1 of 6 — the diagonal fixed-point predicate.** `DiagFixed P a n` holds
iff the presented neighbourhood `Xₙ = P.X n` is already `a`-fixed, i.e. (`diagFixed_iff_fixedNbhd_mem`)
iff `Xₙ` is a neighbourhood of Theorem 8.5's subsystem `fixedNbhd a = {X ∈ V ∣ X a X}`. -/
def DiagFixed (P : ComputablePresentation V) (a : ApproximableMap V V) (n : ℕ) : Prop :=
  a.rel (P.X n) (P.X n)

/-- `DiagFixed P a n` is exactly `(fixedNbhd a).mem (P.X n)`, since `P.X n` is always already a
`V`-neighbourhood (`P.mem_X`). -/
theorem diagFixed_iff_fixedNbhd_mem (P : ComputablePresentation V) (a : ApproximableMap V V)
    (n : ℕ) : DiagFixed P a n ↔ (fixedNbhd a).mem (P.X n) :=
  (and_iff_right (P.mem_X n)).symm

/-- **`DiagFixed P a` is recursively enumerable, given `a` is a computable map.** Restrict
`ComputableMap`'s two-variable relation `Xₙ a Xₘ` to the diagonal `n = m` via `REPred.comp`
against the primitive-recursive pairing `n ↦ Nat.pair n n`. -/
theorem diagFixed_isREPred {P : ComputablePresentation V} {a : ApproximableMap V V}
    (ha : ComputableMap P P a) : REPred (DiagFixed P a) := by
  have ha' : REPred (fun t : ℕ => a.rel (P.X t.unpair.1) (P.X t.unpair.2)) := ha.out
  have hdiag : Nat.Primrec (fun n : ℕ => Nat.pair n n) := primrec_id.pair primrec_id
  refine REPred.of_iff (fun n => ?_) (ha'.comp hdiag)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact Iff.rfl

/-- **The decidable witness relation underlying `DiagFixed`'s r.e.-ness, extracted.** Unfolding
`REPred`'s own definition (`p n ↔ ∃ i, q ⟨i,n⟩` with `q` recursively decidable via a `{0,1}`-valued
primitive-recursive `qChar`) exposes `qChar` directly: `DiagFixed P a n ↔ ∃ i, qChar ⟨i,n⟩ = 1`.
This is the "genuinely decidable, no unbounded search" ingredient that Theorem 8.8(c) Parts 2–4 gate
their primitive-recursive fold on. -/
theorem diagFixed_exists_qChar {P : ComputablePresentation V} {a : ApproximableMap V V}
    (ha : ComputableMap P P a) :
    ∃ qChar : ℕ → ℕ, Nat.Primrec qChar ∧
      ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1 := by
  obtain ⟨q, hq, hqe⟩ := diagFixed_isREPred ha
  obtain ⟨f, hf, hfe⟩ := hq
  exact ⟨f, hf, fun n => (hqe n).trans (exists_congr (fun i => hfe _))⟩

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

/-- **One step of the `qChar`-gated fold.** The accumulator `r` is a raw index (no `(ok,idx)` pair
needed); `e` codes the next list entry `⟨i, n⟩ = Nat.pair i n`. If `qChar e = 1` (a checked
`qChar`-witness for `n := e.unpair.2`) *and* `cons (Nat.pair r n) = 1` (`r`, `n` are `V`-consistent),
advance to `P.inter r n`; otherwise no-op (skip this entry). -/
def myStep (r e : ℕ) : ℕ :=
  selectFn (isOne (qChar e) * isOne (cons (Nat.pair r e.unpair.2)))
    (P.inter r e.unpair.2) r

/-- **The `qChar`-gated fold**, starting from `P.masterIdx`. -/
def myFold (l : List ℕ) : ℕ := l.foldl (myStep P qChar cons) P.masterIdx

@[simp] theorem myFold_nil : myFold P qChar cons [] = P.masterIdx := rfl

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

/-- `foldCode`-shaped step matching `myStep`: state `w = pair e (pair r params)` (`params`
unused). -/
def myStepCode (w : ℕ) : ℕ := myStep P qChar cons w.unpair.2.unpair.1 w.unpair.1

/-- The code-level `qChar`-gated fold. -/
def myFoldCode (c : ℕ) : ℕ := foldCode (myStepCode P qChar cons) 0 P.masterIdx c

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

/-- **The base case: `P.masterIdx` is always `DiagFixed`.** `P.X P.masterIdx = V.master`
(`masterIdx_spec`), and `a.rel V.master V.master` holds for every approximable map (`master_rel`). -/
theorem diagFixed_masterIdx (a : ApproximableMap V V) : DiagFixed P a P.masterIdx := by
  show a.rel (P.X P.masterIdx) (P.X P.masterIdx)
  rw [P.masterIdx_spec]
  exact a.master_rel
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

theorem myFoldCode_eq (c : ℕ) : myFoldCode P qChar cons c = myFold P qChar cons (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => myStepCode P qChar cons (Nat.pair x (Nat.pair acc 0)))
      = myStep P qChar cons := by
    funext acc x
    unfold myStepCode
    simp only [unpair_pair_fst, unpair_pair_snd]
  unfold myFoldCode myFold
  rw [foldCode_eq', hfun]
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

theorem myFold_cons (e : ℕ) (rest : List ℕ) :
    myFold P qChar cons (e :: rest) = rest.foldl (myStep P qChar cons) (myStep P qChar cons P.masterIdx e) := by
  unfold myFold; rw [List.foldl_cons]
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}

/-- **One-step preservation of `DiagFixed`.** If the accumulator `r` is already `DiagFixed` and
`e`'s gate succeeds (`qChar e = 1` giving `DiagFixed` of the raw index `e.unpair.2` via `hqChar`, and
`cons (Nat.pair r e.unpair.2) = 1` giving a `V`-consistency witness), then `myStep P qChar cons r e`
is `DiagFixed` too — via `fixedNbhd_subsystem a`'s `inter_closed` plus `P.inter_spec`. If the gate
fails, the step no-ops and the invariant is preserved trivially. -/
theorem myStep_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {r : ℕ} (hr : DiagFixed P a r) (e : ℕ) :
    DiagFixed P a (myStep P qChar cons r e) := by
  unfold myStep
  have hq_dec : ((qChar e) ≠ 1) ∨ ((qChar e) = 1) := by
    by_cases hq : (qChar e) = 1
    · exact Or.inr hq
    · exact Or.inl hq
  rcases hq_dec with hq | hq
  · rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
    exact hr
  · rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair r e.unpair.2)) ≠ 1) ∨ ((cons (Nat.pair r e.unpair.2)) = 1) := by
      by_cases hc : (cons (Nat.pair r e.unpair.2)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero]
      exact hr
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one]
      have hn : DiagFixed P a e.unpair.2 :=
        (hqChar e.unpair.2).mpr ⟨e.unpair.1, by rw [pair_unpair]; exact hq⟩
      obtain ⟨k, hk⟩ := (hcons r e.unpair.2).mp hc
      have hVinter : V.mem (P.X r ∩ P.X e.unpair.2) := by
        rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
      have hfix : (fixedNbhd a).mem (P.X r ∩ P.X e.unpair.2) :=
        (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a r).mp hr)
          ((diagFixed_iff_fixedNbhd_mem P a e.unpair.2).mp hn) hVinter
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]
      exact hfix

/-- **The fold invariant, over an arbitrary starting accumulator.** -/
theorem myFold_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {r : ℕ}, DiagFixed P a r → DiagFixed P a (l.foldl (myStep P qChar cons) r) := by
  induction l with
  | nil => intro r hr; simpa using hr
  | cons e rest ih =>
    intro r hr
    rw [List.foldl_cons]
    exact ih (myStep_diagFixed_of_diagFixed hqChar hcons hr e)

/-- **Correctness of the `qChar`-gated fold, instantiated at the real starting point
`P.masterIdx`.** -/
theorem myFold_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    DiagFixed P a (myFold P qChar cons l) :=
  myFold_diagFixed_of_diagFixed hqChar hcons l (diagFixed_masterIdx a)

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)
variable {P qChar cons}
variable (P qChar cons)

/-- **Theorem 8.8(c), Part 2 of 6, headline invariant.** `myFoldCode qChar cons c` is `DiagFixed`
for *every* list-code `c` — no matter what garbage `c` decodes to, the fold only ever advances past
checked (`qChar`-witnessed, `V`-consistent) steps, so the output always lands back inside
`fixedNbhd a`. -/
theorem diagFixed_myFoldCode {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c : ℕ) :
    DiagFixed P a (myFoldCode P qChar cons c) := by
  rw [myFoldCode_eq]
  exact myFold_diagFixed hqChar hcons (decodeList c)

theorem primrec_myStepCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myStepCode P qChar cons) := by
  have he : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) := Nat.Primrec.right.comp he
  have hargs : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    hr.pair he2
  have hqchar_e : Nat.Primrec (fun w : ℕ => qChar w.unpair.1) := hqCharp.comp he
  have hcons_val : Nat.Primrec
      (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)) :=
    hconsp.comp hargs
  have hcond : Nat.Primrec (fun w : ℕ =>
      isOne (qChar w.unpair.1) * isOne (cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))) :=
    primrec_mul₂ (primrec_isOne.comp hqchar_e) (primrec_isOne.comp hcons_val)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    (P.inter_primrec.comp hargs).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hinter hr).of_eq fun _ => rfl

/-- **`myFoldCode` is primitive recursive** (Part 2's headline `Nat.Primrec` claim). -/
theorem primrec_myFoldCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myFoldCode P qChar cons) :=
  (primrec_foldCode (primrec_myStepCode P qChar cons hqCharp hconsp)
    (Nat.Primrec.const 0) (Nat.Primrec.const P.masterIdx) primrec_id).of_eq
    fun _ => rfl

end

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

section
open Domain.Recursive NeighborhoodSystem

/-- A fixed code for the rational pair `(0,1)`, presenting `U.master`. -/
def masterPairCode : ℕ := Nat.pair zeroCode oneCode

@[simp] theorem decodeRatPair_masterPairCode : decodeRatPair masterPairCode = ((0 : ℚ), (1 : ℚ)) := by
  unfold masterPairCode decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_zeroCode, decodeRat_oneCode]

/-- A fixed index of `U.master = Ico 0 1`. -/
def UmasterIdx : ℕ := encodeQPairList [((0 : ℚ), (1 : ℚ))]

/-- The singleton list-code `[masterPairCode]` decodes to the singleton presenting list of
`U.master`. -/
theorem decodeQPairList_masterCode :
    decodeQPairList (Nat.pair masterPairCode 0 + 1) = [((0 : ℚ), (1 : ℚ))] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  simp [decodeRatPair_masterPairCode]

/-- **A list all of whose pairs are already non-degenerate is empty iff it presents `∅`** (unlike
an arbitrary presenting list, where individually-degenerate pairs could make this fail). -/
theorem presentedIntervals_eq_empty_iff_of_forall_lt {L' : List (ℚ × ℚ)}
    (hpos : ∀ p ∈ L', p.1 < p.2) : presentedIntervals L' = ∅ ↔ L' = [] := by
  constructor
  · intro h
    rcases L' with _ | ⟨a, l⟩
    · rfl
    · exact absurd h (Set.Nonempty.ne_empty ⟨a.1, mem_presentedIntervals.mpr
        ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _,
          hpos a (List.mem_cons.mpr (Or.inl rfl))⟩⟩)
  · rintro rfl; exact presentedIntervals_nil

theorem presentedIntervals_filter_qpPos (L : List (ℚ × ℚ)) :
    presentedIntervals (L.filter (fun p => decide (p.1 < p.2))) = presentedIntervals L := by
  ext x
  simp only [mem_presentedIntervals, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx1, hx2⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hx1 hx2⟩, hx1, hx2⟩

theorem presentedIntervals_singleton_zero_one :
    presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
  rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]; rfl

/-- Clip a rational pair to `[0,1)`, moving `r` up to `0` and `s` down to `1` when needed. Mirrors
`Definition87.lean`'s `private def clip`, redefined here (public) since `canonList`/`canonCode` need
both a list-level and a code-level version of it. -/
def qpClip (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ 0, p.2 ⊓ 1)

/-- **Canonicalize** an arbitrary presenting list into one that presents a genuine
`U`-neighbourhood: clip every pair into `[0,1)` and discard degenerate pairs, falling back to the
single pair `(0,1)` (presenting `U.master`) if nothing survives. -/
def canonList (L : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  match (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with
  | [] => [((0 : ℚ), (1 : ℚ))]
  | L' => L'

/-- Unfolding equation for `canonList` on the `cons` branch. -/
theorem canonList_eq_of_filter_eq_cons {L : List (ℚ × ℚ)} {a : ℚ × ℚ} {l : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = a :: l) :
    canonList L = a :: l := by
  unfold canonList; rw [h]

/-- Unfolding equation for `canonList` on the `nil` branch, stated so `rw` can fire on a literal
occurrence of `canonList L` (rather than needing to see through the `match`). -/
theorem canonList_eq_of_filter_eq_nil {L : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = []) :
    canonList L = [((0 : ℚ), (1 : ℚ))] := by
  unfold canonList; rw [h]

theorem presentedIntervals_map_qpClip (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map qpClip) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ico, qpClip]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hx0, hx1⟩
    exact ⟨(q.1 ⊔ 0, q.2 ⊓ 1), ⟨q, hq, rfl⟩, sup_le hxq1 hx0, lt_inf_iff.mpr ⟨hxq2, hx1⟩⟩

/-- **`canonList` always presents a genuine `U`-neighbourhood.** -/
theorem U_mem_presentedIntervals_canonList (L : List (ℚ × ℚ)) :
    U.mem (presentedIntervals (canonList L)) := by
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · rw [canonList_eq_of_filter_eq_nil hL]
    have heq : presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
      rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]; rfl
    rw [heq]; exact U.master_mem
  · rw [canonList_eq_of_filter_eq_cons hL]
    have hL'eq : presentedIntervals (a :: l) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
      rw [← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
    have hmem : a ∈ (L.map qpClip).filter (fun p => decide (p.1 < p.2)) := by
      rw [hL]; exact List.mem_cons.mpr (Or.inl rfl)
    have ha : a.1 < a.2 := by simpa using (List.mem_filter.mp hmem).2
    refine ⟨⟨a :: l, rfl⟩, ?_, hL'eq ▸ Set.inter_subset_right⟩
    exact ⟨a.1, mem_presentedIntervals.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _, ha⟩⟩

/-- **`canonList` is a no-op (as a set) on a list that already presents a `U`-neighbourhood.** -/
theorem canonList_fixed {L : List (ℚ × ℚ)} (h : U.mem (presentedIntervals L)) :
    presentedIntervals (canonList L) = presentedIntervals L := by
  obtain ⟨-, hne, hsub⟩ := h
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · exfalso
    have hcontra : presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 = ∅ := by
      rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos (L.map qpClip), hL,
        presentedIntervals_nil]
    rw [Set.inter_eq_left.mpr hsub] at hcontra
    exact hne.ne_empty hcontra
  · rw [canonList_eq_of_filter_eq_cons hL, ← hL, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, Set.inter_eq_left.mpr hsub]

/-- Code-level `qpClip`: `(r,s) ↦ (r⊔0, s⊓1)` on a rational-pair code. -/
def qpClipCode (e : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair e.unpair.1 zeroCode)) (ratMinCode (Nat.pair e.unpair.2 oneCode))

/-- `[qpClipCode e]` if the clipped pair is non-degenerate, else `[]` (the empty list code `0`). -/
def canonFilterStep (e : ℕ) : ℕ :=
  selectFn (qpNonemptyBop (qpClipCode e)) (Nat.pair (qpClipCode e) 0 + 1) 0

/-- The code-level clip-and-filter pass, mirroring the list-level
`(L.map qpClip).filter (fun p => decide (p.1 < p.2))`. -/
def canonListCode (c : ℕ) : ℕ := flatMapCode (fun t => canonFilterStep t.unpair.2) 0 c

/-- **The code-level canonicalization**, mirroring `canonList` exactly: `canonListCode c` if
non-empty, else the fallback singleton `[masterPairCode]` (presenting `U.master`). -/
def canonCode (c : ℕ) : ℕ :=
  selectFn (isZero (canonListCode c)) (Nat.pair masterPairCode 0 + 1) (canonListCode c)

/-- **`𝒰`'s enumeration**: canonicalize the `List (ℚ × ℚ)` coded by `n`. -/
def UX (n : ℕ) : Set ℚ := presentedIntervals (decodeQPairList (canonCode n))

/-- The intersection index: `combineCode` on canonicalized codes (`UX` re-canonicalizes on
lookup, so no further canonicalization is needed here). -/
def Uinter (n m : ℕ) : ℕ := combineCode (canonCode n) (canonCode m)

theorem decodeRatPair_qpClipCode (e : ℕ) :
    decodeRatPair (qpClipCode e) = qpClip (decodeRatPair e) := by
  unfold qpClipCode qpClip decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode, decodeRat_zeroCode, decodeRat_oneCode]

theorem decodeList_canonFilterStep (e : ℕ) :
    decodeList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClipCode e] else [] := by
  unfold canonFilterStep
  by_cases h : qpNonemptyBop (qpClipCode e) = 1
  · rw [h, selectFn_one]
    have h' : (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 :=
      (qpNonemptyBop_eq_one_iff (qpClipCode e)).mp h
    rw [decodeRatPair_qpClipCode] at h'
    simp [h', decodeList_succ, decodeList_zero]
  · have h0 : qpNonemptyBop (qpClipCode e) = 0 := by
      have := ratLtCode_le_one (Nat.pair (qpClipCode e).unpair.1 (qpClipCode e).unpair.2)
      unfold qpNonemptyBop at h ⊢; omega
    rw [h0, selectFn_zero]
    have hnot : ¬ (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 := by
      rw [← qpNonemptyBop_eq_one_iff]; omega
    rw [decodeRatPair_qpClipCode] at hnot
    simp [hnot, decodeList_zero]

theorem decodeQPairList_canonFilterStep (e : ℕ) :
    decodeQPairList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClip (decodeRatPair e)] else [] := by
  unfold decodeQPairList
  rw [decodeList_canonFilterStep]
  split <;> simp [decodeRatPair_qpClipCode]

theorem mem_decodeQPairList_canonFilterStep (e : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonFilterStep e) ↔
      (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2 ∧ p = qpClip (decodeRatPair e) := by
  rw [decodeQPairList_canonFilterStep]
  by_cases h : (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
  · simp [h]
  · simp [h]

/-- **`canonListCode` realizes the clip-and-filter pass at the set level.** -/
theorem mem_decodeQPairList_canonListCode (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonListCode c) ↔
      ∃ p0 ∈ decodeQPairList c, (qpClip p0).1 < (qpClip p0).2 ∧ p = qpClip p0 := by
  unfold canonListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hcond, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep]; exact ⟨hcond, hp⟩⟩

/-- Every element of `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point), so — unlike an arbitrary list — this particular list is empty
iff its `presentedIntervals` is empty. -/
theorem decodeQPairList_canonListCode_eq_nil_iff (c : ℕ) :
    decodeQPairList (canonListCode c) = [] ↔
      presentedIntervals (decodeQPairList (canonListCode c)) = ∅ :=
  (presentedIntervals_eq_empty_iff_of_forall_lt (fun p hp => by
    obtain ⟨p0, hp0, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact hcond)).symm

/-- **`canonListCode` realizes the clip-and-filter pass at the `presentedIntervals` level.** -/
theorem presentedIntervals_decodeQPairList_canonListCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonListCode c))
      = presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1 := by
  rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos ((decodeQPairList c).map qpClip)]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_canonListCode, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨p0, hp0, hcond, rfl⟩
    exact ⟨⟨p0, hp0, rfl⟩, decide_eq_true_eq.mpr hcond⟩
  · rintro ⟨⟨p0, hp0, hp⟩, hcond⟩
    rw [decide_eq_true_eq] at hcond
    exact ⟨p0, hp0, hp ▸ hcond, hp.symm⟩

/-- **`canonCode` realizes `canonList` at the `presentedIntervals` level.** -/
theorem presentedIntervals_decodeQPairList_canonCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonCode c))
      = presentedIntervals (canonList (decodeQPairList c)) := by
  have hfilterPos : ∀ p ∈ ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)),
      p.1 < p.2 := fun p hp => by simpa using (List.mem_filter.mp hp).2
  by_cases hne : (presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1).Nonempty
  · have hnc : (presentedIntervals (decodeQPairList (canonListCode c))).Nonempty := by
      rwa [presentedIntervals_decodeQPairList_canonListCode]
    have hcne : canonListCode c ≠ 0 := by
      intro h
      apply hnc.ne_empty
      unfold decodeQPairList
      rw [h, decodeList_zero, List.map_nil]
      exact presentedIntervals_nil
    have hzero : isZero (canonListCode c) = 0 := by
      by_contra hz
      have h1 := isZero_le_one (canonListCode c)
      exact hcne ((isZero_eq_one_iff _).mp (by omega))
    have hcc : canonCode c = canonListCode c := by unfold canonCode; rw [hzero, selectFn_zero]
    have hL'ne : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) ≠ [] := by
      rw [Ne, ← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos,
        presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
      exact hne.ne_empty
    rcases hL : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
    · exact absurd hL hL'ne
    · rw [hcc, presentedIntervals_decodeQPairList_canonListCode, canonList_eq_of_filter_eq_cons hL,
        ← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hLnil : decodeQPairList (canonListCode c) = [] := by
      rw [decodeQPairList_canonListCode_eq_nil_iff, presentedIntervals_decodeQPairList_canonListCode,
        hne]
    have hczero : canonListCode c = 0 := by
      have h' := hLnil
      unfold decodeQPairList at h'
      rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'
    have hzero : isZero (canonListCode c) = 1 := by rw [hczero]; exact (isZero_eq_one_iff 0).mpr rfl
    have hcc : canonCode c = Nat.pair masterPairCode 0 + 1 := by
      unfold canonCode; rw [hzero, selectFn_one]
    have hLnil' : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) = [] := by
      rw [← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos, presentedIntervals_filter_qpPos,
        presentedIntervals_map_qpClip]
      exact hne
    rw [hcc, decodeQPairList_masterCode, canonList_eq_of_filter_eq_nil hLnil']

theorem UX_eq (n : ℕ) : UX n = presentedIntervals (canonList (decodeQPairList n)) :=
  presentedIntervals_decodeQPairList_canonCode n

theorem UX_UmasterIdx : UX UmasterIdx = U.master := by
  unfold UmasterIdx
  rw [UX_eq, decodeQPairList_encodeQPairList]
  have hmem : U.mem (presentedIntervals [((0 : ℚ), (1 : ℚ))]) := by
    rw [presentedIntervals_singleton_zero_one]; exact U.master_mem
  rw [canonList_fixed hmem, presentedIntervals_singleton_zero_one]

/-- Every `UX n` is a genuine `U`-neighbourhood. -/
theorem U_mem_UX (n : ℕ) : U.mem (UX n) := by
  rw [UX_eq]; exact U_mem_presentedIntervals_canonList _

/-- `UX` is onto `U`'s neighbourhoods: every `U`-neighbourhood already has a Scott-literal
presenting list (`U_mem_iff_scott`), on which `canonList` is a no-op (`canonList_fixed`). -/
theorem U_surj_UX : ∀ {Y : Set ℚ}, U.mem Y → ∃ n, UX n = Y := by
  intro Y hY
  obtain ⟨L, -, hYeq, -⟩ := U_mem_iff_scott.mp hY
  have hUL : U.mem (presentedIntervals L) := by rw [← hYeq]; exact hY
  exact ⟨encodeQPairList L, by
    rw [UX_eq, decodeQPairList_encodeQPairList, canonList_fixed hUL, ← hYeq]⟩

/-- **Scott's consistency condition reduces to non-emptiness**: since `U`'s raw intersection
`combineCode` output is *automatically* a genuine `U`-neighbourhood whenever it is non-empty
(it is always presentable and always `⊆ [0,1)`), "`∃k. Xₖ ⊆ Xₙ∩Xₘ`" holds iff `Xₙ∩Xₘ` is
non-empty (every `Xₖ` being itself non-empty rules out the `⊆ ∅` direction). -/
theorem U_cons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, UX k ⊆ UX n ∩ UX m) ↔ (UX n ∩ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (U_mem_UX k).2.1.mono hk
  · intro hne
    have hUmem : U.mem (UX n ∩ UX m) := by
      obtain ⟨-, -, hsubn⟩ := U_mem_UX n
      exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
        (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
        hne, Set.inter_subset_left.trans hsubn⟩
    obtain ⟨k, hk⟩ := U_surj_UX hUmem
    exact ⟨k, by rw [hk]⟩

theorem Uinter_spec {n m : ℕ} (h : ∃ k, UX k ⊆ UX n ∩ UX m) : UX (Uinter n m) = UX n ∩ UX m := by
  have hne : (UX n ∩ UX m).Nonempty := (U_cons_iff_nonempty_inter n m).mp h
  have hUL : U.mem (presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_combineCode]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
      (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
      hne, Set.inter_subset_left.trans hsubn⟩
  unfold Uinter UX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL,
    presentedIntervals_decodeQPairList_combineCode]

theorem primrec_qpClipCode : Nat.Primrec qpClipCode := by
  have h1 : Nat.Primrec (fun e : ℕ => e.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun e : ℕ => e.unpair.2) := Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h1.pair (Nat.Primrec.const zeroCode))).pair
    (primrec_ratMinCode.comp (h2.pair (Nat.Primrec.const oneCode)))).of_eq fun _ => rfl

theorem primrec_canonFilterStep : Nat.Primrec canonFilterStep := by
  have hc : Nat.Primrec qpClipCode := primrec_qpClipCode
  exact (primrec_selectFn (primrec_qpNonemptyBop.comp hc)
    (Nat.Primrec.succ.comp (hc.pair (Nat.Primrec.const 0))) (Nat.Primrec.const 0)).of_eq
    fun _ => rfl

theorem primrec_canonListCode : Nat.Primrec canonListCode := by
  have hg : Nat.Primrec (fun t : ℕ => canonFilterStep t.unpair.2) :=
    primrec_canonFilterStep.comp Nat.Primrec.right
  exact ((primrec_flatMapCode hg).comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq
    fun c => by
      unfold canonListCode
      simp only [id, unpair_pair_fst, unpair_pair_snd]

theorem primrec_canonCode : Nat.Primrec canonCode :=
  (primrec_selectFn (primrec_isZero.comp primrec_canonListCode)
    (Nat.Primrec.const (Nat.pair masterPairCode 0 + 1)) primrec_canonListCode).of_eq
    fun _ => rfl

/-- **7.1(ii) for `𝒰`**: consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable, via
`U_cons_iff_nonempty_inter` and `recDecidable_presentedIntervals_nonempty`. -/
theorem U_cons_computable : RecDecidable₂ (fun n m => ∃ k, UX k ⊆ UX n ∩ UX m) := by
  unfold RecDecidable₂
  have hcomb : Nat.Primrec (fun t : ℕ => combineCode (canonCode t.unpair.1) (canonCode t.unpair.2)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
      (primrec_canonCode.comp Nat.Primrec.right))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable_presentedIntervals_nonempty.comp hcomb)
  show (∃ k, UX k ⊆ UX t.unpair.1 ∩ UX t.unpair.2) ↔ _
  rw [U_cons_iff_nonempty_inter, UX, UX, presentedIntervals_decodeQPairList_combineCode]

/-- **7.1(i) for `𝒰`**: `Xₙ ∩ Xₘ = X_k` is recursively decidable. Reduces to
`recDecidable₂_presentedIntervals_eq` on the codes `combineCode (canonCode n) (canonCode m)`
(realizing `Xₙ ∩ Xₘ`) and `canonCode k` (realizing `X_k`). -/
theorem U_interEq_computable : RecDecidable₃ (fun n m k => UX n ∩ UX m = UX k) := by
  unfold RecDecidable₃
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h3 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcomb : Nat.Primrec (fun t : ℕ =>
      combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp h1).pair (primrec_canonCode.comp h2))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hg : Nat.Primrec (fun t : ℕ =>
      Nat.pair (combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1))
        (canonCode t.unpair.2.unpair.2)) := hcomb.pair (primrec_canonCode.comp h3)
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable₂_presentedIntervals_eq.comp hg)
  show UX t.unpair.1 ∩ UX t.unpair.2.unpair.1 = UX t.unpair.2.unpair.2 ↔ _
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [UX, UX, UX, presentedIntervals_decodeQPairList_combineCode]

theorem Uinter_primrec : Nat.Primrec (fun t : ℕ => Uinter t.unpair.1 t.unpair.2) := by
  unfold Uinter
  exact (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Theorem 8.8(b), Part 3.** `𝒰` (Definition 8.7) has a genuine `ComputablePresentation`. -/
def UComputablePresentation : ComputablePresentation U where
  X := UX
  mem_X := U_mem_UX
  surj := U_surj_UX
  interEq_computable := U_interEq_computable
  cons_computable := U_cons_computable
  inter := Uinter
  inter_primrec := Uinter_primrec
  inter_spec := Uinter_spec
  masterIdx := UmasterIdx
  masterIdx_spec := UX_UmasterIdx

/-- **`𝒰` is effectively given.** -/
theorem U_isEffectivelyGiven : U.IsEffectivelyGiven := ⟨UComputablePresentation⟩

/-- `decodeQPairList (canonCode c)` is never empty (it always contains at least the fallback
pair `(0,1)`, or a genuine clipped pair). -/
theorem decodeQPairList_canonCode_ne_nil (c : ℕ) : decodeQPairList (canonCode c) ≠ [] := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one, decodeQPairList_masterCode]
    simp
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro hcontra
    apply hz
    have h' := hcontra
    unfold decodeQPairList at h'
    rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'

/-- `canonCode c` is never the `0` (empty-list) code. -/
theorem canonCode_ne_zero (c : ℕ) : canonCode c ≠ 0 := by
  intro h
  exact decodeQPairList_canonCode_ne_nil c (by rw [h]; unfold decodeQPairList; rw [decodeList_zero]; rfl)

/-- Every pair in `decodeQPairList (canonListCode c)` is already non-degenerate (this is
`canonFilterStep`'s whole point). -/
theorem forall_lt_decodeQPairList_canonListCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonListCode c), p.1 < p.2 := fun p hp => by
  obtain ⟨p0, -, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
  exact hcond

/-- **Every pair in `decodeQPairList (canonCode c)` is non-degenerate** — both branches of
`canonCode` (the filtered list, or the `[masterPairCode]` fallback) only ever produce
`p.1 < p.2` pairs. This is what lets `splitU` (Theorem 8.8(b) Part 4) safely pick the *first*
pair of `decodeQPairList (canonCode n)` as its midpoint-split witness, with no search needed. -/
theorem forall_lt_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), p.1 < p.2 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    exact forall_lt_decodeQPairList_canonListCode c

end

end DomainTheory.NeighbourhoodSystems
end

