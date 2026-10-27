module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26

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

/-! ### Theorem 8.8(b)–(c) (moved from Exercise_8_15 monolith) -/

section
open Domain.Recursive NeighborhoodSystem

/-- Clip a rational-pair code `e` to `[decodeRat m, ∞)`, given `t = pair m e`. -/
def clipGeCode (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1)) t.unpair.2.unpair.2

/-- Clip every pair of the list-code `c` into `[decodeRat m, ∞)`. -/
def clipGeListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipGeCode t) 0 + 1) m c

/-- Clip a rational-pair code `e` to `(-∞, decodeRat m)`, given `t = pair m e`. -/
def clipLtCode (t : ℕ) : ℕ :=
  Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1))

/-- Clip every pair of the list-code `c` into `(-∞, decodeRat m)`. -/
def clipLtListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipLtCode t) 0 + 1) m c

/-- The code of the head element of a non-empty list-code `c` (`decodeList c`'s head). Junk
(`0`'s `unpair.1`) when `c = 0`, but we only ever apply it to `canonCode n ≠ 0`
(`canonCode_ne_zero`). -/
def firstElemCode (c : ℕ) : ℕ := (c - 1).unpair.1

/-- Clip a pair up to `[m, ∞)`: clamp the left endpoint at `m`, leave the right endpoint. -/
def qpClipGe (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ m, p.2)

/-- Clip a pair down to `(-∞, m)`: leave the left endpoint, clamp the right endpoint at `m`. -/
def qpClipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

/-- The midpoint code of the first pair of `canonCode n`'s presenting list. -/
def splitMidCode (n : ℕ) : ℕ := ratMidCode (firstElemCode (canonCode n))

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
first presenting pair. -/
def splitULeft (n : ℕ) : ℕ := clipLtListCode (splitMidCode n) (canonCode n)

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitURight (n : ℕ) : ℕ := clipGeListCode (splitMidCode n) (canonCode n)

theorem decodeQPairList_singletonCode (v : ℕ) :
    decodeQPairList (Nat.pair v 0 + 1) = [decodeRatPair v] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  rfl

theorem decodeRatPair_clipGeCode (m e : ℕ) :
    decodeRatPair (clipGeCode (Nat.pair m e)) = qpClipGe (decodeRat m) (decodeRatPair e) := by
  unfold clipGeCode decodeRatPair qpClipGe
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMaxCode]

theorem decodeRatPair_clipLtCode (m e : ℕ) :
    decodeRatPair (clipLtCode (Nat.pair m e)) = qpClipLt (decodeRat m) (decodeRatPair e) := by
  unfold clipLtCode decodeRatPair qpClipLt
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMinCode]

theorem mem_decodeQPairList_clipGeListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipGeListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipGe (decodeRat m) p0 := by
  unfold clipGeListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipGeCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipGeCode]; exact hp⟩

theorem mem_decodeQPairList_clipLtListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipLtListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipLt (decodeRat m) p0 := by
  unfold clipLtListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode]; exact hp⟩

theorem mem_decodeQPairList_firstElemCode {c : ℕ} (hc : c ≠ 0) :
    decodeRatPair (firstElemCode c) ∈ decodeQPairList c := by
  obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  have : firstElemCode (c' + 1) = c'.unpair.1 := by unfold firstElemCode; simp
  unfold decodeQPairList
  rw [this, decodeList_succ]
  exact List.mem_map_of_mem (by simp)

theorem presentedIntervals_map_qpClipGe (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipGe m)) = presentedIntervals L ∩ Set.Ici m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ici, qpClipGe]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2⟩, le_sup_right.trans hx1⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1 ⊔ m, q.2), ⟨q, hq, rfl⟩, sup_le hxq1 hxm, hxq2⟩

theorem presentedIntervals_decodeQPairList_clipGeListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipGeListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Ici (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipGe]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipGeListCode, List.mem_map]
  simp only [eq_comm]

theorem presentedIntervals_map_qpClipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, qpClipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

theorem presentedIntervals_decodeQPairList_clipLtListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipLtListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Iio (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipLt]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipLtListCode, List.mem_map]
  simp only [eq_comm]

theorem primrec_clipGeCode : Nat.Primrec clipGeCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair (primrec_ratMaxCode.comp (he1.pair hm)) he2).of_eq
    fun t => by simp only [clipGeCode]

theorem primrec_clipGeListCode : Nat.Primrec (fun t : ℕ => clipGeListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipGeCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipGeCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

theorem primrec_clipLtCode : Nat.Primrec clipLtCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair he1 (primrec_ratMinCode.comp (he2.pair hm))).of_eq
    fun t => by simp only [clipLtCode]

theorem primrec_clipLtListCode : Nat.Primrec (fun t : ℕ => clipLtListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipLtCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipLtCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

theorem primrec_firstElemCode : Nat.Primrec firstElemCode :=
  Nat.Primrec.left.comp primrec_pred

theorem primrec_splitMidCode : Nat.Primrec splitMidCode :=
  (primrec_ratMidCode.comp (primrec_firstElemCode.comp primrec_canonCode)).of_eq fun n => by
    simp only [splitMidCode]

theorem primrec_splitULeft : Nat.Primrec splitULeft :=
  (primrec_clipLtListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitULeft, unpair_pair_fst, unpair_pair_snd]

theorem primrec_splitURight : Nat.Primrec splitURight :=
  (primrec_clipGeListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitURight, unpair_pair_fst, unpair_pair_snd]

/-- The first pair `p₀` of `canonCode n`'s presenting list is non-degenerate, `p₀.1 < p₀.2`. -/
theorem splitU_p0_lt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < (decodeRatPair (firstElemCode (canonCode n))).2 :=
  forall_lt_decodeQPairList_canonCode n _
    (mem_decodeQPairList_firstElemCode (canonCode_ne_zero n))

theorem splitU_mid_gt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < decodeRat (splitMidCode n) := by
  show decodeRat (firstElemCode (canonCode n)).unpair.1 < decodeRat (splitMidCode n)
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact left_lt_add_div_two.mpr h

theorem UX_splitULeft (n : ℕ) :
    UX (splitULeft n) = UX n ∩ Set.Iio (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitULeft n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨(decodeRatPair (firstElemCode (canonCode n))).1, ?_, splitU_mid_gt n⟩
      exact mem_presentedIntervals.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), le_refl _, splitU_p0_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitULeft n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

theorem splitU_mid_lt (n : ℕ) :
    decodeRat (splitMidCode n) < (decodeRatPair (firstElemCode (canonCode n))).2 := by
  show decodeRat (splitMidCode n) < decodeRat (firstElemCode (canonCode n)).unpair.2
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact add_div_two_lt_right.mpr h

theorem UX_splitURight (n : ℕ) :
    UX (splitURight n) = UX n ∩ Set.Ici (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitURight n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · refine ⟨decodeRat (splitMidCode n), ?_, Set.self_mem_Ici⟩
      exact mem_presentedIntervals.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), (splitU_mid_gt n).le, splitU_mid_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitURight n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

/-- **Theorem 8.8(b) Part 4, disjointness**: `splitULeft`/`splitURight` cover disjoint pieces. -/
theorem splitU_disjoint (n : ℕ) : UX (splitULeft n) ∩ UX (splitURight n) = ∅ := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

/-- **Theorem 8.8(b) Part 4, properness (left)**: `splitULeft n` is a *proper* subset of `Xₙ`. -/
theorem splitU_left_ne (n : ℕ) : UX (splitULeft n) ≠ UX n := by
  intro hEq
  have hZsub : UX (splitURight n) ⊆ UX (splitULeft n) := by
    rw [hEq, UX_splitURight]; exact Set.inter_subset_left
  have hZempty : UX (splitURight n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter hZsub subset_rfl
  exact (U_mem_UX (splitURight n)).2.1.ne_empty (Set.subset_empty_iff.mp hZempty)

/-- **Theorem 8.8(b) Part 4, properness (right)**: `splitURight n` is a *proper* subset of `Xₙ`. -/
theorem splitU_right_ne (n : ℕ) : UX (splitURight n) ≠ UX n := by
  intro hEq
  have hYsub : UX (splitULeft n) ⊆ UX (splitURight n) := by
    rw [hEq, UX_splitULeft]; exact Set.inter_subset_left
  have hYempty : UX (splitULeft n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter subset_rfl hYsub
  exact (U_mem_UX (splitULeft n)).2.1.ne_empty (Set.subset_empty_iff.mp hYempty)

/-- **Theorem 8.8(b) Part 4, covering**: `splitULeft`/`splitURight` reunite to `Xₙ`. -/
theorem splitU_union (n : ℕ) : UX (splitULeft n) ∪ UX (splitURight n) = UX n := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitMidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Swap `0` and `P.masterIdx`.** A primitive-recursive involution on `ℕ` re-pointing whichever
index `P.masterIdx` names `D`'s master neighbourhood to sit at index `0` instead, leaving every
other index fixed. -/
def eIdx (n : ℕ) : ℕ :=
  if n = 0 then P.masterIdx else if n = P.masterIdx then 0 else n

theorem eIdx_involutive : Function.Involutive (eIdx P) := by
  intro n
  unfold eIdx
  split_ifs with h0 hm hm' hm'' hm''' <;> simp_all

theorem eIdx_primrec : Nat.Primrec (eIdx P) := by
  have hc0 : Nat.Primrec (fun n => isZero n) := primrec_isZero
  have hcm : Nat.Primrec (fun n : ℕ => isZero ((n - P.masterIdx) + (P.masterIdx - n))) :=
    primrec_isZero.comp
      (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const P.masterIdx))
        (primrec_sub₂ (Nat.Primrec.const P.masterIdx) primrec_id))
  have hinner : Nat.Primrec (fun n : ℕ =>
      selectFn (isZero ((n - P.masterIdx) + (P.masterIdx - n))) 0 n) :=
    primrec_ite hcm (Nat.Primrec.const 0) primrec_id
  refine (primrec_ite hc0 (Nat.Primrec.const P.masterIdx) hinner).of_eq (fun n => ?_)
  rcases (show isZero n = 0 ∨ isZero n = 1 from by have := isZero_le_one n; omega) with h0 | h0
  · rw [h0, selectFn_zero]
    have hn0 : n ≠ 0 := by intro h; subst h; unfold isZero at h0; omega
    rcases (show isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 0 ∨
        isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 1 from
        by have := isZero_le_one ((n - P.masterIdx) + (P.masterIdx - n)); omega) with h1 | h1
    · rw [h1, selectFn_zero]
      have hnm : n ≠ P.masterIdx := by intro h; subst h; unfold isZero at h1; omega
      unfold eIdx
      rw [ite_eq_right hn0, ite_eq_right hnm]
    · rw [h1, selectFn_one]
      have hnm : n = P.masterIdx := by unfold isZero at h1; omega
      unfold eIdx
      rw [ite_eq_right hn0, ite_eq_left hnm]
  · rw [h0, selectFn_one]
    have hn0 : n = 0 := by unfold isZero at h0; omega
    unfold eIdx
    rw [ite_eq_left hn0]

/-- **The re-pointed presentation `P₀`**: `P`'s enumeration reindexed by `eIdx`, so that
`P₀.X 0 = D.master`. Built via `ComputablePresentation.reindexInvolutive`, so every one of Scott's
structural fields — in particular the two deciders `interEq_computable`/`cons_computable` needed
for `DAtom_recDecidable` — transfers automatically, with no need to redo Part 5's work. -/
noncomputable def P0 : ComputablePresentation D :=
  P.reindexInvolutive (eIdx P) (eIdx_involutive P) (eIdx_primrec P)

@[simp] theorem P0_X (n : ℕ) : (P0 P).X n = P.X (eIdx P n) := rfl

/-- **The `(pos, neg)` accumulator pair for a sign sequence `δ`, at depth `n`.** Mirrors
`genAtom`'s own recursion: at step `n`, `n` itself joins `pos` (if `δ n = true`) or `neg`
(otherwise). -/
def posnegList (δ : ℕ → Bool) : ℕ → List ℕ × List ℕ
  | 0 => ([], [])
  | n + 1 =>
      let pn := posnegList δ n
      if δ n then (pn.1 ++ [n], pn.2) else (pn.1, pn.2 ++ [n])

/-- **`e := P₀.X`, Scott's re-enumeration with `e 0 = D.master`.** -/
noncomputable abbrev e : ℕ → Set α := (P0 P).X


@[simp] theorem posnegList_zero (δ : ℕ → Bool) : posnegList δ 0 = ([], []) := rfl

theorem posnegList_succ_true {δ : ℕ → Bool} {n : ℕ} (h : δ n = true) :
    posnegList δ (n + 1) = ((posnegList δ n).1 ++ [n], (posnegList δ n).2) := by
  show (if δ n then _ else _) = _
  simp [h]

theorem posnegList_succ_false {δ : ℕ → Bool} {n : ℕ} (h : δ n = false) :
    posnegList δ (n + 1) = ((posnegList δ n).1, (posnegList δ n).2 ++ [n]) := by
  show (if δ n then _ else _) = _
  simp [h]

/-- `IPos` splits across list append (order/multiplicity are irrelevant to membership). -/
theorem IPos_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E) (l1 l2 : List ℕ) :
    IPos Q (l1 ++ l2) = IPos Q l1 ∩ IPos Q l2 := by
  induction l1 with
  | nil => simp [IPos_nil]
  | cons a l ih => rw [List.cons_append, IPos_cons, IPos_cons, ih, Set.inter_assoc]

/-- The negative part of `DAtom` splits across list append. -/
theorem negPart_append {E : NeighborhoodSystem α} (Q : ComputablePresentation E)
    (n1 n2 : List ℕ) :
    {m : ℕ | ∀ j ∈ (n1 ++ n2), m ∉ idxSet Q.X j} =
      {m | ∀ j ∈ n1, m ∉ idxSet Q.X j} ∩ {m | ∀ j ∈ n2, m ∉ idxSet Q.X j} := by
  ext m
  simp only [Set.mem_ofPred_eq, List.forall_mem_append, Set.mem_inter_iff]

/-- **`genAtom` reindexed via `idxSet e` matches `DAtom (P0 P)` at the `posnegList`
accumulator.** The heart of Part 6c: since `(P0 P).X = e P`, this is exactly the fact that a
`D`-side atom (Boolean-sequence style) and its `(pos, neg)`-list-style description agree. -/
theorem genAtom_eq_DAtom (δ : ℕ → Bool) :
    ∀ n, genAtom (idxSet (e P)) Set.univ δ n =
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 := by
  intro n
  induction n with
  | zero => simp [genAtom, DAtom, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (δ n) with h | h
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_true h, ih]
      unfold DAtom
      rw [IPos_append]
      have hI : IPos (P0 P) [n] = idxSet (e P) n := by
        rw [IPos_cons, IPos_nil, Set.inter_univ]
      rw [hI]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ idxSet (e P) n = _
      ac_rfl
    · have hstep : genAtom (idxSet (e P)) Set.univ δ (n + 1) =
          genAtom (idxSet (e P)) Set.univ δ n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ δ n ∩
          (if δ n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [h]
      rw [hstep, posnegList_succ_false h, ih]
      unfold DAtom
      rw [negPart_append]
      have hZ : {m : ℕ | m ∉ idxSet (e P) n} = Set.univ \ idxSet (e P) n := by
        ext m; simp [Set.mem_sdiff]
      have hn : {m : ℕ | ∀ j ∈ [n], m ∉ idxSet (e P) j} = {m : ℕ | m ∉ idxSet (e P) n} := by
        ext m; simp
      rw [hn, hZ]
      show IPos (P0 P) (posnegList δ n).1 ∩ {m | ∀ j ∈ (posnegList δ n).2, m ∉ idxSet (e P) j}
          ∩ (Set.univ \ idxSet (e P) n) = _
      ac_rfl

theorem eIdx_zero : eIdx P 0 = P.masterIdx := ite_eq_left rfl

/-- **Part 6c's headline result.** `genAtom`-emptiness (for the reindexed enumeration `e P`, at any
sign sequence `δ` and depth `n`) reduces to `DAtom (P0 P)`-emptiness at the `posnegList`
accumulator — which Part 5's `DAtom_recDecidable (P0 P)` already decides, in the codes of *any*
list representing `(posnegList δ n).1`/`.2`. What remains for Part 6e is exactly to realize
`posnegList δ n`'s two components as *codes*, primitively in `n` and a code for `δ`'s first `n`
bits — composing that with `DAtom_recDecidable (P0 P)`'s extracted decider then decides
`genAtom`-emptiness outright, with no need to redo any of Part 5's meet-fold machinery. -/
theorem genAtom_empty_iff (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔
      DAtom (P0 P) (posnegList δ n).1 (posnegList δ n).2 = ∅ := by
  rw [genAtom_eq_DAtom]

theorem hcover : ∀ S, D.mem S ↔ ∃ n, S = e P n := by
  intro S
  constructor
  · intro hS
    obtain ⟨n, hn⟩ := P.surj hS
    exact ⟨eIdx P n, by show S = P.X (eIdx P (eIdx P n)); rw [eIdx_involutive P n]; exact hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact (P0 P).mem_X n

theorem he0 : e P 0 = D.master := by
  show P.X (eIdx P 0) = D.master
  rw [eIdx_zero]; exact P.masterIdx_spec

/-- **`∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j` is recursively decidable in `(i, j)`.** This
transfers (`embed_subset_iff`, twice) to `∃ k, e P k ⊆ e P i ∧ e P k ⊆ e P j`, which is literally
`(P0 P).cons_computable`'s own predicate — reused with no new `Nat.Primrec` work. -/
theorem DprimeU_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff (e P) k t.unpair.1, ← embed_subset_iff (e P) k t.unpair.2])

/-- **The intersection index transfers.** `(P0 P).inter n m` — Scott's own primitive-recursive
intersection index for `D` (reused verbatim, no new index function) — also indexes `Yidx (e P) n ∩
Yidx (e P) m` whenever that intersection is consistent. -/
theorem DprimeU_inter_spec {n m : ℕ}
    (h : ∃ k, Yidx (e P) k ⊆ Yidx (e P) n ∩ Yidx (e P) m) :
    Yidx (e P) ((P0 P).inter n m) = Yidx (e P) n ∩ Yidx (e P) m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff (e P) k n).mpr hk.1)
      ((embed_subset_iff (e P) k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec n m ((P0 P).inter n m)
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp hidx).symm

def capNegCode (t : ℕ) : ℕ := encodeList [t.unpair.2.unpair.2]

theorem capNegCode_eq (a : ℕ) : encodeList [a] = Nat.pair a 0 + 1 := rfl

def capPosCode (t : ℕ) : ℕ := encodeList [t.unpair.1, t.unpair.2.unpair.1]

theorem capPosCode_eq (a b : ℕ) : encodeList [a, b] = Nat.pair a (Nat.pair b 0 + 1) + 1 :=
  rfl

/-- **`idxSet`-intersection, characterized by a single `DAtom` emptiness query.** For *any*
computable presentation `Q`, `idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k` iff `Q.X k` refines both
`Q.X i` and `Q.X j` (Scott's own decidable inclusion) *and* the depth-2 atom `DAtom Q [i,j] [k]`
(positive constraints `{i,j}`, negative constraint `{k}`) is empty. The three pieces are each
decidable (`incl_computable` used twice, `DAtom_recDecidable` at a fixed 2-element/1-element list
pair), so this is
the bridge that lets Part 5's `DAtom` apparatus decide `idxSet`-level *equations*, not just
emptiness. -/
theorem idxSet_inter_eq_iff_DAtom {β : Type*} {V : NeighborhoodSystem β}
    (Q : ComputablePresentation V) (i j k : ℕ) :
    idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k ↔
      Q.X k ⊆ Q.X i ∧ Q.X k ⊆ Q.X j ∧ DAtom Q [i, j] [k] = ∅ := by
  have hDAtom_iff : DAtom Q [i, j] [k] = ∅ ↔ idxSet Q.X i ∩ idxSet Q.X j ⊆ idxSet Q.X k := by
    have hIPos : IPos Q [i, j] = idxSet Q.X i ∩ idxSet Q.X j := by
      rw [IPos_cons, IPos_cons, IPos_nil, Set.inter_univ]
    have hDAtom_eq : DAtom Q [i, j] [k] = (idxSet Q.X i ∩ idxSet Q.X j) \ idxSet Q.X k := by
      show IPos Q [i, j] ∩ {m | ∀ j' ∈ ([k] : List ℕ), m ∉ idxSet Q.X j'} = _
      rw [hIPos]
      ext m
      simp [Set.mem_sdiff]
    rw [hDAtom_eq, Set.sdiff_eq_empty]
  constructor
  · intro heq
    have h1 : idxSet Q.X k ⊆ idxSet Q.X i := by rw [← heq]; exact Set.inter_subset_left
    have h2 : idxSet Q.X k ⊆ idxSet Q.X j := by rw [← heq]; exact Set.inter_subset_right
    exact ⟨(idxSet_subset_iff Q.X k i).mp h1, (idxSet_subset_iff Q.X k j).mp h2,
      hDAtom_iff.mpr heq.subset⟩
  · rintro ⟨hki, hkj, hempty⟩
    exact Set.Subset.antisymm (hDAtom_iff.mp hempty)
      (Set.subset_inter ((idxSet_subset_iff Q.X k i).mpr hki) ((idxSet_subset_iff Q.X k j).mpr hkj))

/-- **`Yidx (e P) i ⊆ Yidx (e P) j`, reindexed.** A thin wrapper packaging two `incl_computable`-style
facts (`(P0 P).X k ⊆ (P0 P).X i`, resp. `j`) as `RecDecidable₃`, ready to combine with the `DAtom`
decider above. -/
theorem inclK_i_recDecidable :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem inclK_j_recDecidable :
    RecDecidable₃ (fun _ j k => (P0 P).X k ⊆ (P0 P).X j) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.left.comp Nat.Primrec.right)
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_capNegCode : Nat.Primrec capNegCode := by
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.2) 0) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  refine (primrec_add₂ hinner (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capNegCode t
  rw [capNegCode, capNegCode_eq]

theorem primrec_capPosCode : Nat.Primrec capPosCode := by
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.1) 0 + 1) :=
    primrec_add₂ (Nat.Primrec.pair h2 (Nat.Primrec.const 0)) (Nat.Primrec.const 1)
  have houter : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.1 0 + 1)) :=
    Nat.Primrec.pair Nat.Primrec.left hinner
  refine (primrec_add₂ houter (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capPosCode t
  rw [capPosCode, capPosCode_eq]

/-- **`DAtom (P0 P) [i, j] [k] = ∅` is recursively decidable in `(i, j, k)`.** Reindexes
`DAtom_recDecidable (P0 P)` (Part 5) along the codes of the fixed-shape lists `[i,j]`/`[k]`. -/
theorem DAtom_pair_recDecidable :
    RecDecidable₃ (fun i j k => DAtom (P0 P) [i, j] [k] = ∅) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (capPosCode t) (capNegCode t)) :=
    primrec_capPosCode.pair primrec_capNegCode
  have hp := (DAtom_recDecidable (P0 P)).comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd, capPosCode, capNegCode, decodeList_encodeList]

/-- **Part 6's headline decidability result.** `Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k` is
recursively decidable in `(i, j, k)`: it transfers (`transfer_inter_eq_iff`) to the `idxSet`-level
equation, which `idxSet_inter_eq_iff_DAtom` reduces to two `incl_computable` queries and one
`DAtom_recDecidable` query — all already decidable. -/
theorem DprimeU_interEq_computable :
    RecDecidable₃ (fun i j k => Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable P |>.and (inclK_j_recDecidable P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
      (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _),
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

/-- **Part 6's final assembly.** Theorem 8.8(a)'s own subsystem `DprimeU D (e P) (hcover P) (he0 P)`
(no new construction — the *same* classical `D'`, built via `splitChoice`, that already witnesses
`D ≅ᴰ D'` and `D' ◁ U`) is **effectively given**: its enumeration is `Yidx (e P)` (classical, exactly
like `unitPresentation`'s constant `X`), and its two index relations reduce, via the transfer lemmas
above, to facts already decided by `P0 P`'s own deciders and Part 5's `DAtom_recDecidable`. -/
noncomputable def DprimeUPresentation :
    ComputablePresentation (DprimeU D (e P) (hcover P) (he0 P)) where
  X n := Yidx (e P) n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeU_interEq_computable P
  cons_computable := DprimeU_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeU_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yidx_zero D (e P) (hcover P) (he0 P)

/-- **Theorem 8.8(b), Part 6.** If `D` is effectively given, then Theorem 8.8(a)'s own subsystem
`D'` (with `D ≅ᴰ D'` and `D' ◁ U`, from `isomorphic_DprimeU`/`DprimeU_subsystem`) is *also*
effectively given. -/
theorem DprimeU_isEffectivelyGiven :
    (DprimeU D (e P) (hcover P) (he0 P)).IsEffectivelyGiven :=
  ⟨DprimeUPresentation P⟩

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)

/-- Pack `(remK, posC, negC, uCode)` into a single state code. -/
def packState (remK posC negC uCode : ℕ) : ℕ := Nat.pair remK (Nat.pair posC (Nat.pair negC uCode))

def stateCode (s : ℕ) : ℕ := s.unpair.2.unpair.2.unpair.2

def stateNeg (s : ℕ) : ℕ := s.unpair.2.unpair.2.unpair.1

def statePos (s : ℕ) : ℕ := s.unpair.2.unpair.1

def stateRem (s : ℕ) : ℕ := s.unpair.1

@[simp] theorem stateRem_packState (a b c d : ℕ) : stateRem (packState a b c d) = a := by
  unfold stateRem packState; simp only [unpair_pair_fst]

@[simp] theorem statePos_packState (a b c d : ℕ) : statePos (packState a b c d) = b := by
  unfold statePos packState; simp only [unpair_pair_fst, unpair_pair_snd]

@[simp] theorem stateNeg_packState (a b c d : ℕ) : stateNeg (packState a b c d) = c := by
  unfold stateNeg packState; simp only [unpair_pair_fst, unpair_pair_snd]

@[simp] theorem stateCode_packState (a b c d : ℕ) : stateCode (packState a b c d) = d := by
  unfold stateCode packState; simp only [unpair_pair_snd]

/-- The initial state at depth `0`: no constraints yet (`posC = negC = 0`, the empty-list code),
`U`-side code is `U.master`'s (`UmasterIdx`), and the unconsumed bit-source is the whole of `k`. -/
def atomBase (k : ℕ) : ℕ := packState k 0 0 UmasterIdx

end AtomCode

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The extracted `D`-atom-emptiness decider for `P0 P`.** Obtained non-constructively
(`Classical.choice`, via `RecDecidable`'s bare existential) from `DAtom_recDecidable (P0 P)`; the
resulting *function* is exactly as computable as any other `Nat.Primrec` function in this
codebase — only *naming* it needs choice, mirroring `DprimeUPresentation`'s own `noncomputable`.
Wrapped in `isOne` so the result is *literally* `{0,1}`-valued (not just "`= 1` iff ..."): `(vii)(1)`'s
`selectFn`-based case analysis on `emptyI`/`emptyJ` needs the *exact* value `0` on the false side, not
merely `≠ 1` (`selectFn`, unlike a genuine `if`, is only well-behaved on a literal `0`/`1` condition). -/
noncomputable def datomDec : ℕ → ℕ := fun n => isOne ((DAtom_recDecidable (P0 P)).choose n)

/-- **The bit-sequence associated to a bit-source `k`**: `deltaOf k i = true` iff bit `i` of `k`
(read low-bit-first, matching `atomStep`'s `remK % 2`/`remK / 2` peeling) is `1`. -/
def deltaOf (k : ℕ) : ℕ → Bool := fun i => decide ((k / 2 ^ i) % 2 = 1)

end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Theorem88d
open NeighborhoodSystem Domain.Recursive

section
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

private def encodeBits (δ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => encodeBits δ n + (if δ n then 2 ^ n else 0)
end

end DomainTheory.NeighbourhoodSystems.Theorem88d
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`unionUX n m` codes `UX n ∪ UX m`.** Canonicalizes both inputs first (mirroring `Uinter`),
then concatenates; the result is always a genuine `U`-neighbourhood since a union of two such is
again presentable, non-empty, and `⊆ [0,1)`. -/
def unionUX (n m : ℕ) : ℕ := Domain.Recursive.appendCode (canonCode n) (canonCode m)

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)

/-- Extract the packed `(remK, posC, negC, uCode)` state from `w = pair k (pair y state)`. -/
def wState (w : ℕ) : ℕ := w.unpair.2.unpair.2

/-- Extract the current depth `y` from a packed step-input `w = pair k (pair y state)`. -/
def wY (w : ℕ) : ℕ := w.unpair.2.unpair.1

/-- **The per-step state transition.** `datomDec` should be `DAtom_recDecidable (P0 P)`'s extracted
decider (`datomDec (pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅`);
kept abstract here so `Nat.Primrec`-ness can be proved once and reused. `bit := remK % 2`, then:
`posC' := pair y posC + 1` / `negC' := pair y negC + 1` are the candidate accumulators with the
current index `y` prepended; `emptyI`/`emptyJ` decide whether the "+"/"-"-refinements are already
`D`-side empty; the new `U`-code either stays `0` (junk, `D`-side empty), is carried over unchanged
(the refinement equals the old atom outright), or is `splitULeft`/`splitURight` of the old code
(a genuine split). -/
def atomStep (datomDec : ℕ → ℕ) (w : ℕ) : ℕ :=
  let y := wY w
  let s := wState w
  let bit := stateRem s % 2
  let posC' := Nat.pair y (statePos s) + 1
  let negC' := Nat.pair y (stateNeg s) + 1
  let emptyI := datomDec (Nat.pair posC' (stateNeg s))
  let emptyJ := datomDec (Nat.pair (statePos s) negC')
  packState (stateRem s / 2) (selectFn bit posC' (statePos s)) (selectFn bit (stateNeg s) negC')
    (selectFn bit
      (selectFn emptyI 0 (selectFn emptyJ (stateCode s) (splitULeft (stateCode s))))
      (selectFn emptyJ 0 (selectFn emptyI (stateCode s) (splitURight (stateCode s)))))

end AtomCode

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The full state recursion**, packing `atomBase`/`atomStep (datomDec P)` via `Nat.Primrec.prec`:
`atomUCodeState P (pair k n)` is the depth-`n` state for bit-source `k`. -/
noncomputable def atomUCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomBase t.unpair.1) (fun y IH => atomStep (datomDec P) (Nat.pair t.unpair.1 (Nat.pair y IH)))

/-- **The depth-`n` `U`-side code**, for bit-source `k` (meaningful exactly when the matching
`D`-side atom, `DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))`, is
non-empty — see `genAtom_atomUCode` below). -/
noncomputable def atomUCode (n k : ℕ) : ℕ := stateCode (atomUCodeState P (Nat.pair k n))

/-- **The depth-`n` accumulated negative-index code**, for bit-source `k`. -/
noncomputable def atomUNeg (n k : ℕ) : ℕ := stateNeg (atomUCodeState P (Nat.pair k n))

/-- **The depth-`n` accumulated positive-index code**, for bit-source `k`. -/
noncomputable def atomUPos (n k : ℕ) : ℕ := statePos (atomUCodeState P (Nat.pair k n))

/-- **`D`-side atom emptiness at depth `n`, for bit-source `k`** — `1` iff the accumulated
`(pos, neg)` constraint pair already denotes the empty `D`-index atom. -/
noncomputable def atomUEmpty (n k : ℕ) : ℕ := datomDec P (Nat.pair (atomUPos P n k) (atomUNeg P n k))

/-- One step of the depth-`n` union fold over bit-sources `i + 2ⁿ` (bit `n` forced `1`): silently
skip over `D`-side-empty ("junk") atoms — whose code is frozen at the aliasing value `0`
(`atomUCode_eq_zero_of_empty`) and would otherwise contribute the spurious `UX 0 = U.master` to the
union — and union in every genuine (non-junk) atom's code via `unionUX`. The accumulator is packed
as `(found, code)`: `found = 0` means "no genuine atom seen among the earlier `i' < i` yet" (`code`
is junk and unused in that case); `found = 1` means `code` already holds the union of all genuine
atoms seen so far. -/
noncomputable def yFoldStep (w : ℕ) : ℕ :=
  let n := w.unpair.1
  let i := w.unpair.2.unpair.1
  let acc := w.unpair.2.unpair.2
  let k := i + 2 ^ n
  selectFn (atomUEmpty P (n + 1) k) acc
    (selectFn acc.unpair.1
      (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) k)))
      (Nat.pair 1 (atomUCode P (n + 1) k)))

/-- The depth-`n` union fold over `i < N`, starting from the "nothing found yet" accumulator
`(0, 0)`. -/
noncomputable def yFold (n N : ℕ) : ℕ :=
  N.rec (Nat.pair 0 0) (fun i acc => yFoldStep P (Nat.pair n (Nat.pair i acc)))

/-- **`YseqCode`, Scott's `Yₙ` coded.** The `Nat.Primrec` union, over the `2ⁿ` bit-sources
`i < 2ⁿ` (bit `n` forced `1`, i.e. `i + 2ⁿ`), of the genuine (non-junk) atoms `atomUCode P (n+1)
(i + 2ⁿ)`. -/
noncomputable def YseqCode (n : ℕ) : ℕ := (yFold P n (2 ^ n)).unpair.2

/-- **`Yc P`, the `Set`-valued family underlying `YseqCode`** — the code-native analogue of
`Theorem88.lean`'s abstract `Yseq`, used to state the `genAtom`-closed-form correspondence below. -/
def Yc (m : ℕ) : Set ℚ := UX (YseqCode P m)

theorem datomDec_spec (posC negC : ℕ) :
    datomDec P (Nat.pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅ := by
  unfold datomDec
  rw [isOne_eq_one_iff]
  have h := (DAtom_recDecidable (P0 P)).choose_spec.2 (Nat.pair posC negC)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

theorem datomDec_le_one (n : ℕ) : datomDec P n ≤ 1 := by unfold datomDec; exact isOne_le_one _

/-- `DAtom` gains a positive constraint by intersecting with `idxSet`, prepended. -/
theorem DAtom_cons_pos (Q : ComputablePresentation D) (i : ℕ) (pos neg : List ℕ) :
    DAtom Q (i :: pos) neg = idxSet Q.X i ∩ DAtom Q pos neg := by
  unfold DAtom; rw [IPos_cons, Set.inter_assoc]

/-- `DAtom` gains a negative constraint by intersecting with the complement of `idxSet`, prepended. -/
theorem DAtom_cons_neg (Q : ComputablePresentation D) (j : ℕ) (pos neg : List ℕ) :
    DAtom Q pos (j :: neg) = (Set.univ \ idxSet Q.X j) ∩ DAtom Q pos neg := by
  ext m
  simp only [mem_DAtom, List.mem_cons, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, true_and,
    mem_idxSet]
  constructor
  · rintro ⟨hpos, hneg⟩
    exact ⟨hneg j (Or.inl rfl), hpos, fun i hi => hneg i (Or.inr hi)⟩
  · rintro ⟨hj, hpos, hneg⟩
    exact ⟨hpos, fun i hi => hi.elim (fun h => h ▸ hj) (hneg i)⟩

/-- **Unfolding `atomUCodeState` one step.** -/
theorem atomUCodeState_succ (k n : ℕ) :
    atomUCodeState P (Nat.pair k (n + 1)) =
      atomStep (datomDec P) (Nat.pair k (Nat.pair n (atomUCodeState P (Nat.pair k n)))) := by
  unfold atomUCodeState
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- The unconsumed bit-source at depth `n` is exactly `k / 2 ^ n` (peeled one bit at a time). -/
theorem stateRem_atomUCodeState (k n : ℕ) : stateRem (atomUCodeState P (Nat.pair k n)) = k / 2 ^ n := by
  induction n with
  | zero => simp [atomUCodeState, atomBase]
  | succ n ih =>
    rw [atomUCodeState_succ]
    unfold atomStep
    simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateRem_packState, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

theorem deltaOf_eq_true_iff (k i : ℕ) : deltaOf k i = true ↔ (k / 2 ^ i) % 2 = 1 := by
  unfold deltaOf; simp

/-- `atomUPos`/`atomUNeg` step by prepending the new index `n` on whichever side `deltaOf k n`
selects, exactly mirroring `genAtom`'s own step. -/
theorem atomUPos_succ (k n : ℕ) :
    atomUPos P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2) (Nat.pair n (atomUPos P n k) + 1) (atomUPos P n k) := by
  unfold atomUPos
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, statePos_packState,
    stateRem_atomUCodeState]

theorem atomUNeg_succ (k n : ℕ) :
    atomUNeg P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2) (atomUNeg P n k) (Nat.pair n (atomUNeg P n k) + 1) := by
  unfold atomUNeg
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateNeg_packState,
    stateRem_atomUCodeState]

/-- **Per-step `D`-side correctness.** The accumulated `(pos, neg)` code pair at depth `n`, for
bit-source `k`, tracks exactly the same atom as `genAtom (idxSet (e P)) Set.univ (deltaOf k) n`. -/
theorem genAtom_atomUCode (k : ℕ) :
    ∀ n, genAtom (idxSet (e P)) Set.univ (deltaOf k) n
      = DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
  intro n
  induction n with
  | zero =>
    simp [genAtom, atomUPos, atomUNeg, atomUCodeState, atomBase, DAtom, decodeList_zero, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hbit1 : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp hδ
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit1, selectFn_one, selectFn_one,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos, Set.inter_comm]
    · have hbit0 : (k / 2 ^ n) % 2 = 0 := by
        rcases Nat.eq_zero_or_pos ((k / 2 ^ n) % 2) with h | h
        · exact h
        · exact absurd ((deltaOf_eq_true_iff k n).mpr (by omega)) (by simp [hδ])
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit0, selectFn_zero, selectFn_zero,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg, Set.inter_comm]

theorem atomUEmpty_eq_one_iff (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
  datomDec_spec P _ _

/-- **`atomUEmpty` reads off `genAtom`'s own emptiness**, via `genAtom_atomUCode`. -/
theorem atomUEmpty_eq_one_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n = ∅ := by
  rw [atomUEmpty_eq_one_iff, ← genAtom_atomUCode]

theorem atomUEmpty_eq_zero_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 0 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n ≠ ∅ := by
  have hle : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
  have h1 := atomUEmpty_eq_one_iff_genAtom P n k
  constructor
  · intro h0 hempty; exact absurd (h1.mpr hempty) (by omega)
  · intro hne; by_contra h0; exact hne (h1.mp (by omega))

theorem atomUPos_zero (k : ℕ) : atomUPos P 0 k = 0 := by
  simp [atomUPos, atomUCodeState, atomBase]

theorem atomUNeg_zero (k : ℕ) : atomUNeg P 0 k = 0 := by
  simp [atomUNeg, atomUCodeState, atomBase]

theorem atomUCode_zero (k : ℕ) : atomUCode P 0 k = UmasterIdx := by
  simp [atomUCode, atomUCodeState, atomBase]

theorem atomUCode_succ (k n : ℕ) :
    atomUCode P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (selectFn (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))) 0
          (selectFn (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)))
            (atomUCode P n k) (splitULeft (atomUCode P n k))))
        (selectFn (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) 0
          (selectFn (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
            (atomUCode P n k) (splitURight (atomUCode P n k)))) := by
  unfold atomUCode atomUPos atomUNeg
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateCode_packState,
    stateRem_atomUCodeState]

/-- The two hypothetical checks appearing in `atomUCode_succ` are exactly `atomUEmpty` at depth
`n + 1`, evaluated at whichever of the two bit-sources through `n` realizes each hypothesis. In
particular, for the *actual* bit-source `k` itself: whichever branch `(k/2^n)%2` selects reproduces
`atomUEmpty P (n+1) k` verbatim. -/
theorem atomUEmpty_succ (k n : ℕ) :
    atomUEmpty P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
        (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) := by
  unfold atomUEmpty
  rw [atomUPos_succ, atomUNeg_succ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp only [hbit, selectFn_zero, selectFn_one]

/-- **Congruence for the whole packed triple**: bit-sources agreeing on `deltaOf` below `n` produce
identical `(pos, neg, code)` triples at depth `n` — the code-level analogue of `genAtom_congr`/
`atomU_congr`, proved jointly (the three components interact through `atomUCode_succ`'s two
`datomDec` checks, which read `atomUPos`/`atomUNeg` at depth `n`). -/
theorem atomUCodeState_congr {n : ℕ} :
    ∀ {k k' : ℕ}, (∀ i < n, deltaOf k i = deltaOf k' i) →
      atomUPos P n k = atomUPos P n k' ∧ atomUNeg P n k = atomUNeg P n k' ∧
        atomUCode P n k = atomUCode P n k' := by
  induction n with
  | zero =>
    intro k k' _
    exact ⟨(atomUPos_zero P k).trans (atomUPos_zero P k').symm,
      (atomUNeg_zero P k).trans (atomUNeg_zero P k').symm,
      (atomUCode_zero P k).trans (atomUCode_zero P k').symm⟩
  | succ n ih =>
    intro k k' h
    obtain ⟨ihpos, ihneg, ihcode⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hbit : (k / 2 ^ n) % 2 = (k' / 2 ^ n) % 2 := by
      have hh := h n (Nat.lt_succ_self n)
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with h2 | h2 <;>
          simp_all [deltaOf]
    refine ⟨?_, ?_, ?_⟩
    · rw [atomUPos_succ, atomUPos_succ, ihpos, hbit]
    · rw [atomUNeg_succ, atomUNeg_succ, ihneg, hbit]
    · rw [atomUCode_succ, atomUCode_succ, ihpos, ihneg, ihcode, hbit]

theorem genAtom_succ_subset (k n : ℕ) :
    genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) ⊆
      genAtom (idxSet (e P)) Set.univ (deltaOf k) n :=
  Set.inter_subset_left

theorem atomUEmpty_mono {n k : ℕ} (h : atomUEmpty P n k = 1) : atomUEmpty P (n + 1) k = 1 := by
  rw [atomUEmpty_eq_one_iff_genAtom] at h ⊢
  exact Set.subset_eq_empty (genAtom_succ_subset P k n) h

theorem atomUEmpty_zero_of_succ {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) : atomUEmpty P n k = 0 := by
  by_contra hne
  have hle := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  have h1 : atomUEmpty P n k = 1 := by unfold atomUEmpty at hne hle ⊢; omega
  exact absurd (atomUEmpty_mono P h1) (by omega)

/-- **Junk is frozen at `0`.** Once a bit-source's `D`-side atom is empty, its `U`-code stays `0`
forever after (both hypothetical continuations of an already-empty atom are themselves empty, so
`atomUCode_succ`'s outer `selectFn` always lands on its `0` branch). -/
theorem atomUCode_eq_zero_of_empty {n k : ℕ} (h : atomUEmpty P n k = 1) :
    atomUCode P (n + 1) k = 0 := by
  have hemp : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
    (atomUEmpty_eq_one_iff P n k).mp h
  have hI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1 := by
    refine (datomDec_spec P _ _).mpr ?_
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos]
    exact Set.subset_empty_iff.mp (hemp ▸ Set.inter_subset_right)
  have hJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
    refine (datomDec_spec P _ _).mpr ?_
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg]
    exact Set.subset_empty_iff.mp (hemp ▸ Set.inter_subset_right)
  rw [atomUCode_succ, hI, hJ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp [hbit, selectFn_zero, selectFn_one]

/-- **Monotonicity**: as long as the depth-`(n+1)` atom is still non-empty, its `U`-code's
neighbourhood shrinks from (or coincides with) the depth-`n` one — either the "carry unchanged"
branch fires (equality) or a genuine `splitULeft`/`splitURight` fires (strict `⊆`, `UX_splitULeft`/
`UX_splitURight`). Mirrors `split_fst_subset`/`split_snd_subset` from the abstract `Theorem88.lean`
account, but unconditionally true here since `splitULeft`/`splitURight` need no side hypotheses. -/
theorem atomUCode_subset {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) :
    UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := by
  have hemp := h
  rw [atomUEmpty_succ] at hemp
  rw [atomUCode_succ]
  set posC := atomUPos P n k
  set negC := atomUNeg P n k
  set c := atomUCode P n k
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit
  · simp only [hbit, selectFn_zero] at hemp ⊢
    rw [hemp, selectFn_zero]
    have hle := datomDec_le_one P (Nat.pair (Nat.pair n posC + 1) negC)
    rcases (by omega : datomDec P (Nat.pair (Nat.pair n posC + 1) negC) = 0 ∨
        datomDec P (Nat.pair (Nat.pair n posC + 1) negC) = 1) with h2 | h2
    · rw [h2, selectFn_zero, UX_splitURight]; exact Set.inter_subset_left
    · rw [h2, selectFn_one]
  · simp only [hbit, selectFn_one] at hemp ⊢
    rw [hemp, selectFn_zero]
    have hle := datomDec_le_one P (Nat.pair posC (Nat.pair n negC + 1))
    rcases (by omega : datomDec P (Nat.pair posC (Nat.pair n negC + 1)) = 0 ∨
        datomDec P (Nat.pair posC (Nat.pair n negC + 1)) = 1) with h2 | h2
    · rw [h2, selectFn_zero, UX_splitULeft]; exact Set.inter_subset_left
    · rw [h2, selectFn_one]

/-- **The core `(vii)(1)` result**: at every depth `n`, atoms for bit-sources disagreeing somewhere
below `n` are disjoint on the `U`-side, *provided both are still `D`-side non-empty*. Proved by
induction on `n`, mirroring `atomU_invariant`'s disjointness clause: either the disagreement is
already below `n - 1` (recurse, then shrink both sides via `atomUCode_subset`), or it is exactly at
the last bit (use `atomUCodeState_congr` to identify the shared depth-`(n-1)` ancestor, then
`splitU_disjoint`, since both survive to depth `n` iff that step was a genuine split). -/
theorem atomUCode_disjoint :
    ∀ n k k', atomUEmpty P n k = 0 → atomUEmpty P n k' = 0 → (∃ i < n, deltaOf k i ≠ deltaOf k' i) →
      UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ := by
  intro n
  induction n with
  | zero => intro k k' _ _ ⟨i, hi, _⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro k k' hk hk' ⟨i, hi, hne⟩
    by_cases hagree : ∀ j < n, deltaOf k j = deltaOf k' j
    · have hδn : deltaOf k n ≠ deltaOf k' n := by
        intro heq
        apply hne
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact hagree i hi'
        · exact heq
      obtain ⟨hpos, hneg, hcode⟩ := atomUCodeState_congr P hagree
      rw [atomUCode_succ, atomUCode_succ, hpos, hneg, hcode]
      -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
      rcases Bool.eq_false_or_eq_true (deltaOf k n) with h1 | h1
      · -- `deltaOf k n = true`: `k` takes bit `1`, so `deltaOf k' n` must be `false`.
        have hbitk : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp h1
        have h2 : deltaOf k' n = false := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact absurd (h1.trans h2.symm) hδn
          · exact h2
        have hbitk' : (k' / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k' n).mpr hh) (by simp [h2])
        have hkI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_one] at h; exact h
        have hk'J : datomDec P (Nat.pair (atomUPos P n k') (Nat.pair n (atomUNeg P n k') + 1)) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_zero] at h; exact h
        rw [hpos, hneg] at hkI
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkI, hk'J]
        exact splitU_disjoint (atomUCode P n k')
      · -- `deltaOf k n = false`: `k` takes bit `0`, so `deltaOf k' n` must be `true`.
        have hbitk : (k / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [h1])
        have h2 : deltaOf k' n = true := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact h2
          · exact absurd (h1.trans h2.symm) hδn
        have hbitk' : (k' / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k' n).mp h2
        have hkJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_zero] at h; exact h
        have hk'I : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k') + 1) (atomUNeg P n k')) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_one] at h; exact h
        rw [hpos, hneg] at hkJ
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkJ, hk'I]
        exact (Set.inter_comm _ _).trans (splitU_disjoint (atomUCode P n k'))
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hd : UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ :=
        ih k k' (atomUEmpty_zero_of_succ P hk) (atomUEmpty_zero_of_succ P hk') ⟨j, hj, hjne⟩
      exact Set.subset_eq_empty
        (Set.inter_subset_inter (atomUCode_subset P hk) (atomUCode_subset P hk')) hd

theorem deltaOf_eq_testBit (k i : ℕ) : deltaOf k i = k.testBit i :=
  Nat.testBit_eq_decide_div_mod_eq.symm

/-- Adding `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_add_two_pow_of_lt {n : ℕ} (m : ℕ) {i : ℕ} (hi : i < n) :
    deltaOf (m + 2 ^ n) i = deltaOf m i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_gt hi]

/-- Adding `2ⁿ` to an `m < 2ⁿ` sets exactly bit `n` (no carry beyond it). -/
theorem deltaOf_two_pow_add_self {n m : ℕ} (hm : m < 2 ^ n) : deltaOf (m + 2 ^ n) n = true := by
  rw [deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
  rfl

namespace Theorem88d

private theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | n + 1 => by
      have ih := encodeBits_lt δ n
      have hp := Nat.two_pow_pos n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn <;> simp [hδn] <;> omega

private theorem deltaOf_encodeBits (δ : ℕ → Bool) :
    ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i
  | n + 1, i, hi => by
      have hlt := encodeBits_lt δ n
      show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n + 2 ^ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [deltaOf_add_two_pow_of_lt _ hi']; exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_two_pow_add_self hlt, hδn]
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_eq_testBit, Nat.testBit_lt_two_pow hlt, hδn]

end Theorem88d

theorem exists_atomUEmpty_zero (n : ℕ) : ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  classical
  set δ0 : ℕ → Bool := fun j => decide (n ∈ idxSet (e P) j) with hδ0def
  have hδ0n : δ0 n = true := by
    show decide (n ∈ idxSet (e P) n) = true
    rw [decide_eq_true_iff]; exact self_mem_idxSet (e P) n
  have hstep : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) =
      genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n := by
    show genAtom (idxSet (e P)) Set.univ δ0 n ∩
      (if δ0 n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
    simp [hδ0n]
  have hxn : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n :=
    genAtom_self (idxSet (e P)) Set.univ (Set.mem_univ n) n
  have hmem : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n :=
    ⟨hxn, self_mem_idxSet (e P) n⟩
  have hAne : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) ≠ ∅ := by
    rw [hstep]; exact Set.Nonempty.ne_empty ⟨n, hmem⟩
  set m0 := Theorem88d.encodeBits δ0 n with hm0def
  have hm0lt : m0 < 2 ^ n := Theorem88d.encodeBits_lt δ0 n
  refine ⟨m0, hm0lt, ?_⟩
  rw [atomUEmpty_eq_zero_iff_genAtom]
  have hagree : ∀ j < n + 1, deltaOf (m0 + 2 ^ n) j = δ0 j := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hj']; exact Theorem88d.deltaOf_encodeBits δ0 n j hj'
    · rw [deltaOf_two_pow_add_self hm0lt, hδ0n]
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree]
  exact hAne

/-- **The `D`-side atom splits along any prepended index** (Scott's `Δ = idxSetₙ ∪ (Δ∖idxSetₙ)`,
pulled back through `DAtom`): needed to show that once the "negative refinement" of a nonempty atom
is empty, the atom already coincides with its own "positive refinement" outright. -/
theorem DAtom_union (i : ℕ) (pos neg : List ℕ) :
    DAtom (P0 P) pos neg = DAtom (P0 P) (i :: pos) neg ∪ DAtom (P0 P) pos (i :: neg) := by
  ext m
  simp only [mem_DAtom, Set.mem_union, List.mem_cons, forall_eq_or_imp]
  by_cases hm : (P0 P).X m ⊆ (P0 P).X i <;> tauto

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem U_mem_union_UX (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨-, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨-, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨decodeQPairList (canonCode n) ++ decodeQPairList (canonCode m),
      (presentedIntervals_append _ _).symm⟩, hne1.mono Set.subset_union_left,
    Set.union_subset hsub1 hsub2⟩
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Validity**, the free half of the invariant: `UX` never needs an emptiness hypothesis at all. -/
theorem atomUCode_mem (n k : ℕ) : U.mem (UX (atomUCode P n k)) := U_mem_UX _

theorem atomUEmpty_congr {n k k' : ℕ} (h : ∀ i < n, deltaOf k i = deltaOf k' i) :
    atomUEmpty P n k = atomUEmpty P n k' := by
  obtain ⟨hpos, hneg, -⟩ := atomUCodeState_congr P h
  unfold atomUEmpty
  rw [hpos, hneg]

theorem atomUEmpty_zero_or_one (n k : ℕ) : atomUEmpty P n k = 0 ∨ atomUEmpty P n k = 1 := by
  have h := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  unfold atomUEmpty
  omega

/-- The complementary fact to `datomDec_spec`: whenever the `D`-side atom is *non*-empty,
`datomDec` reads out exactly `0` (not just "`≠ 1`") — needed so `selectFn`'s zero-branch actually
fires in the per-step unfoldings below. -/
theorem datomDec_eq_zero (posC negC : ℕ) (h : DAtom (P0 P) (decodeList posC) (decodeList negC) ≠ ∅) :
    datomDec P (Nat.pair posC negC) = 0 := by
  have hle := datomDec_le_one P (Nat.pair posC negC)
  have hne : datomDec P (Nat.pair posC negC) ≠ 1 := fun he => h ((datomDec_spec P posC negC).mp he)
  omega

/-- Reducing modulo `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_mod_two_pow_of_lt {k n i : ℕ} (hi : i < n) :
    deltaOf (k % 2 ^ n) i = deltaOf k i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_mod_two_pow]
  simp [hi]

/-- **The canonical "positive twin" at depth `n`** shares `k`'s own `(pos, neg, code)` triple, since
it agrees with `k` on every bit below `n` (`atomUCodeState_congr` applied to
`k % 2ⁿ`/`deltaOf_mod_two_pow_of_lt`/`deltaOf_add_two_pow_of_lt`). -/
theorem atomUCodeState_congr_twin (n k : ℕ) :
    atomUPos P n (k % 2 ^ n + 2 ^ n) = atomUPos P n k ∧
      atomUNeg P n (k % 2 ^ n + 2 ^ n) = atomUNeg P n k ∧
      atomUCode P n (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
  have hagree : ∀ i < n, deltaOf (k % 2 ^ n + 2 ^ n) i = deltaOf k i := by
    intro i hi
    rw [deltaOf_add_two_pow_of_lt _ hi, deltaOf_mod_two_pow_of_lt hi]
  exact atomUCodeState_congr P hagree

/-- **Uniqueness of a bit-source below `2ⁿ`**: two bit-sources agreeing on every bit below `n` and
both `< 2ⁿ` are equal (every bit at or above `n` is forced `false` by the bound, so agreement below
`n` becomes agreement everywhere, and `Nat.eq_of_testBit_eq` finishes). -/
theorem eq_of_deltaOf_agree_of_lt_two_pow {n i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hagree : ∀ l < n, deltaOf i l = deltaOf j l) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro l
  rw [← deltaOf_eq_testBit, ← deltaOf_eq_testBit]
  rcases Nat.lt_or_ge l n with hl | hl
  · exact hagree l hl
  · have hile : 2 ^ n ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_lt_two_pow (hi.trans_le hile),
      Nat.testBit_lt_two_pow (hj.trans_le hile)]

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem mem_decodeQPairList_appendCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (Domain.Recursive.appendCode c1 c2) ↔ p ∈ decodeQPairList c1 ∨ p ∈ decodeQPairList c2 := by
  simp only [mem_decodeQPairList, mem_decodeList_appendCode]
  constructor
  · rintro ⟨v, (hv | hv), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, Or.inl hv, rfl⟩
    · exact ⟨v, Or.inr hv, rfl⟩

theorem presentedIntervals_decodeQPairList_appendCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (Domain.Recursive.appendCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∪ presentedIntervals (decodeQPairList c2) := by
  ext x
  simp only [mem_presentedIntervals, Set.mem_union]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    rcases (mem_decodeQPairList_appendCode c1 c2 p).mp hp with hp' | hp'
    · exact Or.inl ⟨p, hp', h1, h2⟩
    · exact Or.inr ⟨p, hp', h1, h2⟩
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inl hp), h1, h2⟩
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inr hp), h1, h2⟩

theorem UX_unionUX (n m : ℕ) : UX (unionUX n m) = UX n ∪ UX m := by
  have hmem : U.mem (presentedIntervals (decodeQPairList (Domain.Recursive.appendCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_appendCode]; exact U_mem_union_UX n m
  show presentedIntervals (decodeQPairList (canonCode (unionUX n m))) = UX n ∪ UX m
  unfold unionUX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hmem,
    presentedIntervals_decodeQPairList_appendCode]
  rfl

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


theorem primrec_atomBase : Nat.Primrec atomBase :=
  ((Nat.Primrec.id).pair ((Nat.Primrec.const 0).pair
    ((Nat.Primrec.const 0).pair (Nat.Primrec.const UmasterIdx)))).of_eq fun k => by
    unfold atomBase packState; simp only [id_eq]

end AtomCode

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_datomDec : Nat.Primrec (datomDec P) :=
  (primrec_isOne.comp (DAtom_recDecidable (P0 P)).choose_spec.1).of_eq fun _ => rfl
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


theorem primrec_stateCode : Nat.Primrec stateCode :=
  Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)

theorem primrec_stateNeg : Nat.Primrec stateNeg :=
  Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)

theorem primrec_statePos : Nat.Primrec statePos := Nat.Primrec.left.comp Nat.Primrec.right

theorem primrec_stateRem : Nat.Primrec stateRem := Nat.Primrec.left

end AtomCode

theorem primrec_unionUX : Nat.Primrec (fun t : ℕ => unionUX t.unpair.1 t.unpair.2) := by
  unfold unionUX
  exact (Domain.Recursive.primrec_appendCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


theorem primrec_wState : Nat.Primrec wState := Nat.Primrec.right.comp Nat.Primrec.right

theorem primrec_wY : Nat.Primrec wY := Nat.Primrec.left.comp Nat.Primrec.right

theorem primrec_atomStep {datomDec : ℕ → ℕ} (hd : Nat.Primrec datomDec) :
    Nat.Primrec (atomStep datomDec) := by
  have hy : Nat.Primrec wY := primrec_wY
  have hs : Nat.Primrec wState := primrec_wState
  have hrem : Nat.Primrec (fun w => stateRem (wState w)) := primrec_stateRem.comp hs
  have hpos : Nat.Primrec (fun w => statePos (wState w)) := primrec_statePos.comp hs
  have hneg : Nat.Primrec (fun w => stateNeg (wState w)) := primrec_stateNeg.comp hs
  have hcode : Nat.Primrec (fun w => stateCode (wState w)) := primrec_stateCode.comp hs
  have hbit : Nat.Primrec (fun w => stateRem (wState w) % 2) := primrec_mod2.comp hrem
  have hposC' : Nat.Primrec (fun w => Nat.pair (wY w) (statePos (wState w)) + 1) :=
    Nat.Primrec.succ.comp (hy.pair hpos)
  have hnegC' : Nat.Primrec (fun w => Nat.pair (wY w) (stateNeg (wState w)) + 1) :=
    Nat.Primrec.succ.comp (hy.pair hneg)
  have hemptyI : Nat.Primrec (fun w => datomDec (Nat.pair
      (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w)))) :=
    hd.comp (hposC'.pair hneg)
  have hemptyJ : Nat.Primrec (fun w => datomDec (Nat.pair (statePos (wState w))
      (Nat.pair (wY w) (stateNeg (wState w)) + 1))) :=
    hd.comp (hpos.pair hnegC')
  have hsplitL : Nat.Primrec (fun w => splitULeft (stateCode (wState w))) :=
    primrec_splitULeft.comp hcode
  have hsplitR : Nat.Primrec (fun w => splitURight (stateCode (wState w))) :=
    primrec_splitURight.comp hcode
  have hcodeBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (selectFn (datomDec (Nat.pair (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w))))
        0 (selectFn (datomDec (Nat.pair (statePos (wState w))
          (Nat.pair (wY w) (stateNeg (wState w)) + 1))) (stateCode (wState w)) (splitULeft (stateCode (wState w)))))
      (selectFn (datomDec (Nat.pair (statePos (wState w))
          (Nat.pair (wY w) (stateNeg (wState w)) + 1))) 0
        (selectFn (datomDec (Nat.pair (Nat.pair (wY w) (statePos (wState w)) + 1) (stateNeg (wState w))))
          (stateCode (wState w)) (splitURight (stateCode (wState w)))))) :=
    primrec_selectFn hbit
      (primrec_selectFn hemptyI (Nat.Primrec.const 0) (primrec_selectFn hemptyJ hcode hsplitL))
      (primrec_selectFn hemptyJ (Nat.Primrec.const 0) (primrec_selectFn hemptyI hcode hsplitR))
  have hrem' : Nat.Primrec (fun w => stateRem (wState w) / 2) := primrec_div2.comp hrem
  have hposBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (Nat.pair (wY w) (statePos (wState w)) + 1) (statePos (wState w))) :=
    primrec_selectFn hbit hposC' hpos
  have hnegBranch : Nat.Primrec (fun w => selectFn (stateRem (wState w) % 2)
      (stateNeg (wState w)) (Nat.pair (wY w) (stateNeg (wState w)) + 1)) :=
    primrec_selectFn hbit hneg hnegC'
  exact (hrem'.pair (hposBranch.pair (hnegBranch.pair hcodeBranch))).of_eq fun w => by
    unfold atomStep packState
    simp only []

end AtomCode

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_atomUCodeState : Nat.Primrec (atomUCodeState P) :=
  (Nat.Primrec.prec primrec_atomBase (primrec_atomStep (primrec_datomDec P))).of_eq fun _t => rfl

theorem primrec_atomUCode : Nat.Primrec (fun t : ℕ => atomUCode P t.unpair.1 t.unpair.2) :=
  (primrec_stateCode.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUNeg : Nat.Primrec (fun t : ℕ => atomUNeg P t.unpair.1 t.unpair.2) :=
  (primrec_stateNeg.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUPos : Nat.Primrec (fun t : ℕ => atomUPos P t.unpair.1 t.unpair.2) :=
  (primrec_statePos.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUEmpty : Nat.Primrec (fun t : ℕ => atomUEmpty P t.unpair.1 t.unpair.2) :=
  ((primrec_datomDec P).comp ((primrec_atomUPos P).pair (primrec_atomUNeg P))).of_eq
    fun _ => rfl

theorem primrec_yFoldStep : Nat.Primrec (yFoldStep P) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h2n : Nat.Primrec (fun w : ℕ => 2 ^ w.unpair.1) := primrec_two_pow hn
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 2 ^ w.unpair.1) :=
    primrec_add₂ hi h2n
  have hn1 : Nat.Primrec (fun w : ℕ => w.unpair.1 + 1) := Nat.Primrec.succ.comp hn
  have hempty : Nat.Primrec (fun w : ℕ =>
      atomUEmpty P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUEmpty P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcode : Nat.Primrec (fun w : ℕ =>
      atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUCode P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => unionUX w.unpair.2.unpair.2.unpair.2
      (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))) :=
    (primrec_unionUX.comp (hval.pair hcode)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (unionUX w.unpair.2.unpair.2.unpair.2
        (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))))
      (Nat.pair 1 (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)))) :=
    primrec_selectFn hfound
      ((Nat.Primrec.const 1).pair hunion)
      ((Nat.Primrec.const 1).pair hcode)
  exact (primrec_selectFn hempty hacc hinner).of_eq fun w => by unfold yFoldStep; simp only []

theorem primrec_yFold : Nat.Primrec (fun t : ℕ => yFold P t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0)) (primrec_yFoldStep P)).of_eq fun _ => rfl

theorem primrec_YseqCode : Nat.Primrec (YseqCode P) := by
  have h2n : Nat.Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow Nat.Primrec.id
  refine (Nat.Primrec.right.comp ((primrec_yFold P).comp (Nat.Primrec.id.pair h2n))).of_eq
    fun n => ?_
  show ((yFold P (Nat.pair n (2 ^ n)).unpair.1 (Nat.pair n (2 ^ n)).unpair.2)).unpair.2 = YseqCode P n
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

/-- Unfolding `yFoldStep` at an explicit `(n, i, acc)` triple. -/
theorem yFoldStep_eq (n i acc : ℕ) :
    yFoldStep P (Nat.pair n (Nat.pair i acc)) =
      selectFn (atomUEmpty P (n + 1) (i + 2 ^ n)) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) (i + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (i + 2 ^ n)))) := by
  unfold yFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem yFold_succ (n N : ℕ) :
    yFold P n (N + 1) = yFoldStep P (Nat.pair n (Nat.pair N (yFold P n N))) := rfl

theorem yFold_zero (n : ℕ) : yFold P n 0 = Nat.pair 0 0 := rfl

theorem yFold_found_le_one (n : ℕ) : ∀ N, (yFold P n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

/-- **The "found" flag exactly tracks existence of a non-junk bit-source below `N`.** -/
theorem yFold_found_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 ↔ ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn (yFold P n N).unpair.1
          (Nat.pair 1 (unionUX (yFold P n N).unpair.2 (atomUCode P (n + 1) (N + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (N + 2 ^ n)))).unpair.1 = 1 := by
        have hle := yFold_found_le_one P n N
        rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf | hf
        · rw [show (yFold P n N).unpair.1 = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

/-- **The membership form of `yFold`'s correctness**: once a non-junk bit-source has been found
below `N`, the running code's `UX`-image is exactly the union of the genuine (non-junk) atoms
seen so far. -/
theorem yFold_mem_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 →
      ∀ z : ℚ, z ∈ UX (yFold P n N).unpair.2 ↔
        ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) := by
  intro N
  induction N with
  | zero => intro h; simp [yFold_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [yFold_succ, yFoldStep_eq] at hfound1 ⊢
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((yFold_found_iff P n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (yFold P n N).unpair.1 = 1 := by
          have := yFold_found_le_one P n N; omega
        rw [hf1, selectFn_one, unpair_pair_snd, UX_unionUX, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

theorem yFold_two_pow_found (n : ℕ) : (yFold P n (2 ^ n)).unpair.1 = 1 :=
  (yFold_found_iff P n (2 ^ n)).mpr (exists_atomUEmpty_zero P n)

/-- **The closed-form membership characterization of `YseqCode`** — the "Set-level closed form"
this part exists to supply: a point lies in `UX (YseqCode P n)` iff it lies in some genuine
(non-junk) depth-`(n+1)` atom with bit `n` forced `1`. -/
theorem mem_UX_YseqCode_iff (n : ℕ) (z : ℚ) :
    z ∈ UX (YseqCode P n) ↔
      ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) :=
  yFold_mem_iff P n (2 ^ n) (yFold_two_pow_found P n) z

/-- **General exclusion lemma**: if a bit-source `k'` is non-junk at depth `n`, and its own
canonical "positive twin" at depth `n + 1` (same bits below `n`, forcing bit `n` to `true`) is
junk, then `k'`'s own depth-`n` atom is disjoint from `YseqCode`'s entire union — no genuine
(non-junk) depth-`(n+1)` atom in the union can leak a point into it, whether that atom *is* `k'`'s
own excluded twin (immediate contradiction) or some *other* twin `i ≠ j` (disjoint at depth `n` by
`atomUCode_disjoint`, since distinct bit-sources below `2ⁿ` always disagree somewhere below `n`,
`eq_of_deltaOf_agree_of_lt_two_pow`). -/
theorem atomUCode_disjoint_YseqCode_of_posTwin_empty {n k' : ℕ} (hk' : atomUEmpty P n k' = 0)
    (hjunk : atomUEmpty P (n + 1) (k' % 2 ^ n + 2 ^ n) = 1) :
    UX (atomUCode P n k') ∩ UX (YseqCode P n) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzB, hzY⟩
  obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
  set j := k' % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k' (Nat.two_pow_pos n)
  have hk'j : ∀ l < n, deltaOf k' l = deltaOf j l := by
    intro l hl; rw [hjdef, deltaOf_mod_two_pow_of_lt hl]
  by_cases hij : i = j
  · rw [hij] at hie; exact absurd hie (by omega)
  · have hdisagree : ∃ l < n, deltaOf (i + 2 ^ n) l ≠ deltaOf k' l := by
      by_contra hcon
      push Not at hcon
      apply hij
      apply eq_of_deltaOf_agree_of_lt_two_pow hilt hjlt
      intro l hl
      have h1 : deltaOf (i + 2 ^ n) l = deltaOf i l := deltaOf_add_two_pow_of_lt _ hl
      have h2 := hcon l hl
      rw [h1] at h2
      exact h2.trans (hk'j l hl)
    obtain ⟨l, hl, hlne⟩ := hdisagree
    have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') = ∅ :=
      atomUCode_disjoint P n (i + 2 ^ n) k' (atomUEmpty_zero_of_succ P hie) hk' ⟨l, hl, hlne⟩
    have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode_subset P hie hz
    have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') := ⟨hzB', hzB⟩
    rw [hd] at hzmem
    exact absurd hzmem (Set.mem_empty_iff_false z).mp

theorem atomUCode_succ_true {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = true) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) ∩ UX (YseqCode P n) := by
  set j := k % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  have hagree : ∀ i < n + 1, deltaOf k i = deltaOf (j + 2 ^ n) i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hi', hjdef, deltaOf_mod_two_pow_of_lt hi']
    · rw [deltaOf_two_pow_add_self hjlt, hδ]
  obtain ⟨hpos_eq, hneg_eq, hcode_eq⟩ := atomUCodeState_congr P hagree
  have hempty_eq : atomUEmpty P (n + 1) (j + 2 ^ n) = 0 := by
    have heq : atomUEmpty P (n + 1) (j + 2 ^ n) = atomUEmpty P (n + 1) k := by
      unfold atomUEmpty; rw [hpos_eq, hneg_eq]
    rw [heq]; exact hne
  apply Set.Subset.antisymm
  · have hsub1 : UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := atomUCode_subset P hne
    have hsub2 : UX (atomUCode P (n + 1) k) ⊆ UX (YseqCode P n) := by
      rw [hcode_eq]
      intro z hz
      exact (mem_UX_YseqCode_iff P n z).mpr ⟨j, hjlt, hempty_eq, hz⟩
    exact Set.subset_inter hsub1 hsub2
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
    by_cases hagree' : ∀ p < n, deltaOf (i + 2 ^ n) p = deltaOf k p
    · have hagreeFull : ∀ l < n + 1, deltaOf (i + 2 ^ n) l = deltaOf k l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
        · exact hagree' l hl'
        · rw [deltaOf_two_pow_add_self hilt, hδ]
      have hcode_eq'' : atomUCode P (n + 1) (i + 2 ^ n) = atomUCode P (n + 1) k :=
        (atomUCodeState_congr P hagreeFull).2.2
      rw [← hcode_eq'']; exact hz
    · push Not at hagree'
      obtain ⟨l, hl, hlne⟩ := hagree'
      have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) = ∅ :=
        atomUCode_disjoint P n (i + 2 ^ n) k (atomUEmpty_zero_of_succ P hie)
          (atomUEmpty_zero_of_succ P hne) ⟨l, hl, hlne⟩
      have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode_subset P hie hz
      have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) := ⟨hzB', hzB⟩
      rw [hd] at hzmem
      exact absurd hzmem (Set.mem_empty_iff_false z).mp

/-- **The junction lemma**: once a bit-source's atom is still non-empty at depth `n` but becomes
junk at depth `n + 1`, `genAtom`'s corresponding step (against `Yc P`/`U.master`) is already
empty. Two cases on `deltaOf k n`: `true` reduces directly to
`atomUCode_disjoint_YseqCode_of_posTwin_empty` (`k` already *is* its own positive twin); `false`
needs the extra fact that the depth-`n` atom's own code is *unchanged* by its positive twin (since
the "negative refinement" being `D`-side empty forces the whole atom into the positive side,
`DAtom_union`), so `atomUCode_succ_true` at the twin identifies `atomUCode P n k` with the
intersection against `YseqCode`'s union outright, i.e. `UX (atomUCode P n k) ⊆ Yc P n`. -/
theorem atomUCode_inter_succ_empty_of_junk {n k : ℕ} (hn0 : atomUEmpty P n k = 0)
    (hjunk : atomUEmpty P (n + 1) k = 1) :
    UX (atomUCode P n k) ∩ (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅ := by
  -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
  rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
  · -- `k` itself already has bit `n` set: `k` is (mod `2 ^ (n + 1)`) its own positive twin.
    have hjlt0 : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    have hagree : ∀ l < n + 1, deltaOf (k % 2 ^ n + 2 ^ n) l = deltaOf k l := by
      intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [deltaOf_add_two_pow_of_lt _ hl', deltaOf_mod_two_pow_of_lt hl']
      · rw [deltaOf_two_pow_add_self hjlt0, hδ]
    obtain ⟨hp, hnge, -⟩ := atomUCodeState_congr P hagree
    have htwinJunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by
      unfold atomUEmpty
      rw [hp, hnge]
      exact hjunk
    rw [ite_eq_left hδ]
    exact atomUCode_disjoint_YseqCode_of_posTwin_empty P hn0 htwinJunk
  · -- `k` has bit `n` unset: the "negative refinement" alone is empty, so `k`'s own atom already
    -- coincides with its positive twin's atom (`DAtom_union`), which forces junk at `n + 1`.
    have hbit0 : (k / 2 ^ n) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
      · exact hh
      · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
    have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
      have h := hjunk
      rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
      exact h
    have hJempty : DAtom (P0 P) (decodeList (atomUPos P n k))
        (n :: decodeList (atomUNeg P n k)) = ∅ := by
      have h := (datomDec_spec P (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)).mp hempJ
      rwa [decodeList_succ, unpair_pair_fst, unpair_pair_snd] at h
    have hDunion := DAtom_union P n (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))
    have hIeqAll : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (n :: decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
      rw [hDunion, hJempty, Set.union_empty]
    have hIeqAll' : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (decodeList (Nat.pair n (atomUPos P n k) + 1)) (decodeList (atomUNeg P n k)) := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]; exact hIeqAll
    have hne0 : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) ≠ ∅ := by
      intro hcon
      have := (atomUEmpty_eq_one_iff P n k).mpr hcon
      omega
    have hemptyI0 : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
      apply datomDec_eq_zero
      rw [← hIeqAll']
      exact hne0
    have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
    have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
      have hh := deltaOf_two_pow_add_self hjlt
      rw [deltaOf_eq_true_iff] at hh
      exact hh
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by
      rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
      exact hemptyI0
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
      rw [atomUCode_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, hemptyI0, selectFn_zero,
        htwinCode, hempJ, selectFn_one]
    rw [htwinCodeVal, htwinCode] at hkey
    have hsub : UX (atomUCode P n k) ⊆ Yc P n := by
      intro z hz
      have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := by rw [← hkey]; exact hz
      exact hz'.2
    rw [ite_eq_right (by simp [hδ])]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz1, -, hz2⟩
    exact hz2 (hsub hz1)

/-- **The closed form, "false"-branch** (mirroring `Theorem88.lean`'s `atomU_succ_eq`'s `else`
case): for non-junk `k` with bit `n` forced `false`, the depth-`(n+1)` atom is the depth-`n` atom
*minus* `YseqCode`. Two sub-cases on whether `k`'s own "positive twin" (bits agreeing below `n`,
bit `n` forced `true`) is itself junk: if junk, the whole depth-`n` atom is already disjoint from
`YseqCode`'s union (`atomUCode_disjoint_YseqCode_of_posTwin_empty`), so subtracting it changes
nothing; if non-junk, the twin's own code is literally `splitULeft (atomUCode P n k)` (unfolding
both `atomUCode_succ`'s at the shared ancestor), so `atomUCode_succ_true` applied to the twin
identifies `splitULeft`'s image with `YseqCode`'s contribution, and `splitU_union`/`splitU_disjoint`
finish the algebra `UX(splitURight c) = UX c \ UX(splitULeft c)`. -/
theorem atomUCode_succ_false {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = false) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
  have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
  have hbit0 : (k / 2 ^ n) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
    · exact hh
    · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
  have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
    have h := hne
    rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
    exact h
  have hncode : atomUCode P (n + 1) k = selectFn
      (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
      (atomUCode P n k) (splitURight (atomUCode P n k)) := by
    rw [atomUCode_succ, hbit0, selectFn_zero, hempJ, selectFn_zero]
  have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
    have hh := deltaOf_two_pow_add_self hjlt
    rw [deltaOf_eq_true_iff] at hh
    exact hh
  have htwinEmpty : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) =
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) := by
    rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
  have hIle := datomDec_le_one P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))
  rcases (by omega :
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 ∨
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1) with hI | hI
  · -- Genuine split at the shared ancestor: the twin's own code is `splitULeft (atomUCode P n k)`.
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = splitULeft (atomUCode P n k) := by
      rw [atomUCode_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, htwinCode, hI, selectFn_zero,
        hempJ, selectFn_zero]
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by rw [htwinEmpty, hI]
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    rw [htwinCodeVal, htwinCode] at hkey
    have hunion := splitU_union (atomUCode P n k)
    have hdisj := splitU_disjoint (atomUCode P n k)
    have hUXeq : UX (splitURight (atomUCode P n k)) =
        UX (atomUCode P n k) \ UX (splitULeft (atomUCode P n k)) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨?_, fun hzL => ?_⟩
        · rw [← hunion]; exact Set.mem_union_right _ hz
        · have hz' : z ∈ UX (splitULeft (atomUCode P n k)) ∩ UX (splitURight (atomUCode P n k)) :=
            ⟨hzL, hz⟩
          rw [hdisj] at hz'
          exact hz'
      · rintro z ⟨hzC, hznL⟩
        rw [← hunion] at hzC
        exact hzC.resolve_left hznL
    rw [hncode, hI, selectFn_zero, hUXeq, hkey]
    apply Set.Subset.antisymm
    · rintro z ⟨hzC, hznCY⟩
      exact ⟨hzC, fun hzY => hznCY ⟨hzC, hzY⟩⟩
    · rintro z ⟨hzC, hznY⟩
      exact ⟨hzC, fun hzY => hznY hzY.2⟩
  · -- Junk twin: the whole depth-`n` atom is already disjoint from `YseqCode`'s union.
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by rw [htwinEmpty, hI]
    have hk : atomUEmpty P n k = 0 := atomUEmpty_zero_of_succ P hne
    have hcdisj : UX (atomUCode P n k) ∩ UX (YseqCode P n) = ∅ :=
      atomUCode_disjoint_YseqCode_of_posTwin_empty P hk htwinNonjunk
    have hEq : UX (atomUCode P n k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨hz, fun hzY => ?_⟩
        have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := ⟨hz, hzY⟩
        rw [hcdisj] at hz'
        exact hz'
      · exact Set.sdiff_subset
    rw [hncode, hI, selectFn_one]
    exact hEq

/-- **The closed-form correspondence** (mirrors `Theorem88.lean`'s `atomU_eq_genAtom`): whenever
`k`'s bit-source is still `D`-side non-empty at depth `n`, the `U`-code `atomUCode P n k` is
*exactly* the generic atom built from `Yc P`/`U.master` — proved by induction, using
`atomUCode_succ_true`/`atomUCode_succ_false` to match `genAtom`'s own recursive step verbatim. -/
theorem atomUCode_eq_genAtomYseqCode (k : ℕ) :
    ∀ n, atomUEmpty P n k = 0 → UX (atomUCode P n k) = genAtom (Yc P) U.master (deltaOf k) n := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [atomUCode_zero, UX_UmasterIdx]
    rfl
  | succ n ih =>
    intro hne
    have ihn := ih (atomUEmpty_zero_of_succ P hne)
    -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ Yc P n := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_true P hne hδ]
      rfl
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ (U.master \ Yc P n) := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_false P hne hδ]
      have hsub : UX (atomUCode P n k) ⊆ U.master := by
        rw [ihn]; exact genAtom_subset (Yc P) U.master (deltaOf k) n
      apply Set.Subset.antisymm
      · intro z hz; exact ⟨hz.1, hsub hz.1, hz.2⟩
      · rintro z ⟨hz1, -, hz2⟩; exact ⟨hz1, hz2⟩

/-- **`Yc P`'s `genAtom`-emptiness matches `atomUEmpty` exactly** (the code-native analogue of
`atomU_invariant`'s emptiness-matching clause "(■)"): combines `atomUCode_eq_genAtomYseqCode`
(non-junk, giving a nonempty `UX`-image) with `atomUCode_inter_succ_empty_of_junk` (the genuine
transition to junk) by induction on `n`. -/
theorem genAtom_Yc_empty_iff (n k : ℕ) :
    genAtom (Yc P) U.master (deltaOf k) n = ∅ ↔ atomUEmpty P n k = 1 := by
  induction n with
  | zero =>
    have h0 : atomUEmpty P 0 k = 0 := by
      have hne : genAtom (idxSet (e P)) Set.univ (deltaOf k) 0 ≠ ∅ := by
        show (Set.univ : Set ℕ) ≠ ∅
        exact Set.univ_nonempty.ne_empty
      exact (atomUEmpty_eq_zero_iff_genAtom P 0 k).mpr hne
    constructor
    · intro h
      exact absurd h (Set.Nonempty.ne_empty U.master_mem.2.1)
    · intro h; omega
  | succ n ih =>
    have hle : atomUEmpty P (n + 1) k ≤ 1 := datomDec_le_one P _
    rcases (by omega : atomUEmpty P (n + 1) k = 0 ∨ atomUEmpty P (n + 1) k = 1) with h1 | h1
    · have heq' := atomUCode_eq_genAtomYseqCode P k (n + 1) h1
      constructor
      · intro hempty
        rw [← heq'] at hempty
        exact absurd hempty (U_mem_UX _).2.1.ne_empty
      · intro hcontra; omega
    · by_cases hn0 : atomUEmpty P n k = 0
      · have heq := atomUCode_eq_genAtomYseqCode P k n hn0
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [← heq]
          exact atomUCode_inter_succ_empty_of_junk P hn0 h1
        exact ⟨fun _ => h1, fun _ => hempty⟩
      · push Not at hn0
        have hle0 : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
        have hn1 : atomUEmpty P n k = 1 := by omega
        have hprev : genAtom (Yc P) U.master (deltaOf k) n = ∅ := ih.mpr hn1
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [hprev, Set.empty_inter]
        exact ⟨fun _ => h1, fun _ => hempty⟩

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Yc_subset_master (n : ℕ) : Yc P n ⊆ U.master := (U_mem_UX (YseqCode P n)).2.2

/-- **`Yc P 0 = U.master`** (Scott's convention `Y₀ = U.master`, matching `Yseq_zero_eq_master`):
the unique bit-source realizing depth `1` with bit `0` set is `k = 1`, whose atom is non-junk
(`idxSet (e P) 0 = Set.univ`, so the "positive" constraint at index `0` is vacuous) and whose code
is literally `UmasterIdx`, since the *negative* sibling constraint (`DAtom (P0 P) [] [0]`) is
already empty — freezing `atomUCode` unchanged through the step (mirrors `atomUCode_subset`'s own
"carry unchanged" branch, here made into an equality). -/
theorem Yc_zero_eq_master : Yc P 0 = U.master := by
  have hidx0 : idxSet (e P) 0 = Set.univ := idxSet_zero D (e P) (hcover P) (he0 P)
  have h01 : atomUEmpty P 1 1 = 0 := by
    apply (atomUEmpty_eq_zero_iff_genAtom P 1 1).mpr
    show genAtom (idxSet (e P)) Set.univ (deltaOf 1) 0 ∩
      (if deltaOf 1 0 then idxSet (e P) 0 else Set.univ \ idxSet (e P) 0) ≠ ∅
    have hδ : deltaOf 1 0 = true := by decide
    rw [hδ, ite_eq_left rfl]
    show (Set.univ : Set ℕ) ∩ idxSet (e P) 0 ≠ ∅
    rw [Set.univ_inter, hidx0]
    exact Set.univ_nonempty.ne_empty
  have hmem : Yc P 0 = UX (atomUCode P 1 1) := by
    unfold Yc
    ext z
    rw [mem_UX_YseqCode_iff]
    constructor
    · rintro ⟨i, hilt, hie, hz⟩
      have hi0 : i = 0 := by have := hilt; omega
      rwa [hi0] at hz
    · intro hz
      exact ⟨0, by norm_num, h01, hz⟩
  rw [hmem]
  have hnn : DAtom (P0 P) [] [] = Set.univ := by unfold DAtom; simp [IPos_nil]
  have hcode : atomUCode P 1 1 = UmasterIdx := by
    have hbit : (1 / 2 ^ (0 : ℕ)) % 2 = 1 := by norm_num
    rw [atomUCode_succ, atomUPos_zero, atomUNeg_zero, hbit, selectFn_one]
    have hposEmpty : datomDec P (Nat.pair (Nat.pair 0 0 + 1) 0) = 0 := by
      apply datomDec_eq_zero
      simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
      show DAtom (P0 P) [0] [] ≠ ∅
      rw [DAtom_cons_pos, hnn, Set.inter_univ, hidx0]
      exact Set.univ_nonempty.ne_empty
    rw [hposEmpty, selectFn_zero]
    have hnegEmpty : datomDec P (Nat.pair 0 (Nat.pair 0 0 + 1)) = 1 := by
      apply (datomDec_spec P _ _).mpr
      simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
      show DAtom (P0 P) [] [0] = ∅
      rw [DAtom_cons_neg, hnn, Set.inter_univ, hidx0, Set.sdiff_self]
    rw [hnegEmpty, selectFn_one, atomUCode_zero]
  rw [hcode, UX_UmasterIdx]

/-- **`δ`'s length-`n` bit-encoding**: the natural number `< 2 ^ n` agreeing with `δ` on every bit
below `n`. -/
def encodeBits (δ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => encodeBits δ n + (if δ n then 2 ^ n else 0)

theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | (n + 1) => by
      have ih := encodeBits_lt δ n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with h | h <;> simp [h] <;> omega

theorem deltaOf_encodeBits (δ : ℕ → Bool) : ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · rcases Bool.eq_false_or_eq_true (δ n) with h | h
      · rw [h, ite_eq_left rfl, deltaOf_add_two_pow_of_lt _ hi']
        exact ih i hi'
      · rw [h, ite_eq_right (by simp), Nat.add_zero]
        exact ih i hi'
    · rw [hi']
      rcases Bool.eq_false_or_eq_true (δ n) with h | h
      · rw [h, ite_eq_left rfl]
        exact deltaOf_two_pow_add_self (encodeBits_lt δ n)
      · rw [h, ite_eq_right (by simp), Nat.add_zero, deltaOf_eq_testBit,
          Nat.testBit_lt_two_pow (encodeBits_lt δ n)]

/-- **The `genAtom`-emptiness core, for arbitrary `δ : ℕ → Bool`.** Realizes `δ`'s first `n` bits
as `deltaOf (encodeBits δ n)` (`genAtom_congr`), then invokes `genAtom_Yc_empty_iff`/
`atomUEmpty_eq_one_iff_genAtom` at that specific bit-source. -/
theorem hcoreIdxYc (δ : ℕ → Bool) (n : ℕ) :
    genAtom (idxSet (e P)) Set.univ δ n = ∅ ↔ genAtom (Yc P) U.master δ n = ∅ := by
  set k := encodeBits δ n with hkdef
  have hagree : ∀ i < n, δ i = deltaOf k i := fun i hi => (deltaOf_encodeBits δ n i hi).symm
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree, genAtom_congr (Yc P) U.master hagree,
    ← atomUEmpty_eq_one_iff_genAtom, genAtom_Yc_empty_iff]

theorem inclK_i_recDecidable_code :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem inclK_j_recDecidable_code :
    RecDecidable₃ (fun _ j k => (P0 P).X k ⊆ (P0 P).X j) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.left.comp Nat.Primrec.right)
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem transfer_dir_idxYc {β1 β2 : Type*} (Z1 : ℕ → Set β1) (M1 : Set β1) (Z2 : ℕ → Set β2)
    (M2 : Set β2) (hcore : ∀ δ n, genAtom Z1 M1 δ n = ∅ ↔ genAtom Z2 M2 δ n = ∅)
    {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n)
    (hne : {x ∈ M1 | ∀ p ∈ cs, (p.2 = true ↔ x ∈ Z1 p.1)}.Nonempty) :
    {y ∈ M2 | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Z2 p.1)}.Nonempty := by
  classical
  obtain ⟨x, hxM, hxcs⟩ := hne
  set δ0 : ℕ → Bool := fun k => decide (x ∈ Z1 k) with hδ0def
  have hX1 : x ∈ genAtom Z1 M1 δ0 n := genAtom_self Z1 M1 hxM n
  have hne1 : (genAtom Z1 M1 δ0 n).Nonempty := ⟨x, hX1⟩
  have hne2 : (genAtom Z2 M2 δ0 n).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h2 => hne1.ne_empty ((hcore δ0 n).mpr h2)
  obtain ⟨y, hy⟩ := hne2
  refine ⟨y, genAtom_subset Z2 M2 δ0 n hy, fun p hp => ?_⟩
  have hforward := genAtom_forward hy p.1 (hn p hp)
  have hbeq : δ0 p.1 = p.2 := by
    show decide (x ∈ Z1 p.1) = p.2
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hxcs p hp).symm
  rwa [hbeq] at hforward

theorem transfer_empty_iff_idxYc {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ cs, (p.2 = true ↔ x ∈ idxSet (e P) p.1)}.Nonempty ↔
      {y ∈ U.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Yc P p.1)}.Nonempty :=
  ⟨transfer_dir_idxYc (idxSet (e P)) Set.univ (Yc P) U.master (hcoreIdxYc P) hn,
    transfer_dir_idxYc (Yc P) U.master (idxSet (e P)) Set.univ (fun δ n => (hcoreIdxYc P δ n).symm)
      hn⟩

theorem transfer_double_subset_iff_idxYc (i j k : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k ↔
      U.master ∩ Yc P i ∩ Yc P j ⊆ Yc P k := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, true), (k, false)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)}
      = ((Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j) \ idxSet (e P) k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = (U.master ∩ Yc P i ∩ Yc P j) \ Yc P k := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      have h1 : y ∈ Yc P i := (hcs (i, true) (by simp)).mp rfl
      have h2 : y ∈ Yc P j := (hcs (j, true) (by simp)).mp rfl
      have h3 : y ∉ Yc P k := fun hmem =>
        absurd ((hcs (k, false) (by simp)).mpr hmem) Bool.false_ne_true
      exact ⟨⟨⟨hyM, h1⟩, h2⟩, h3⟩
    · rintro ⟨⟨⟨hyM, h1⟩, h2⟩, h3⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun _ => h2, fun _ => rfl⟩
      · exact ⟨fun hc => absurd hc Bool.false_ne_true, fun hmem => absurd hmem h3⟩
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_inter_empty_iff_idxYc (i j : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j = ∅ ↔
      U.master ∩ Yc P i ∩ Yc P j = ∅ := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, true)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, true)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)} = (Set.univ : Set ℕ) ∩ idxSet (e P) i ∩ idxSet (e P) j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = U.master ∩ Yc P i ∩ Yc P j := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      exact ⟨⟨hyM, (hcs (i, true) (by simp)).mp rfl⟩, (hcs (j, true) (by simp)).mp rfl⟩
    · rintro ⟨⟨hyM, h1⟩, h2⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun _ => h2, fun _ => rfl⟩
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_subset_iff_idxYc (i j : ℕ) :
    (Set.univ : Set ℕ) ∩ idxSet (e P) i ⊆ idxSet (e P) j ↔
      U.master ∩ Yc P i ⊆ Yc P j := by
  have key := transfer_empty_iff_idxYc P (cs := [(i, true), (j, false)]) (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ (Set.univ : Set ℕ) | ∀ p ∈ [(i, true), (j, false)],
      (p.2 = true ↔ x ∈ idxSet (e P) p.1)} = ((Set.univ : Set ℕ) ∩ idxSet (e P) i) \ idxSet (e P) j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ Yc P p.1)}
      = (U.master ∩ Yc P i) \ Yc P j := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyM, hcs⟩
      have h1 : y ∈ Yc P i := (hcs (i, true) (by simp)).mp rfl
      have h2 : y ∉ Yc P j := fun hmem =>
        absurd ((hcs (j, false) (by simp)).mpr hmem) Bool.false_ne_true
      exact ⟨⟨hyM, h1⟩, h2⟩
    · rintro ⟨⟨hyM, h1⟩, h2⟩
      refine ⟨hyM, fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨fun _ => h1, fun _ => rfl⟩
      · exact ⟨fun hc => absurd hc Bool.false_ne_true, fun hmem => absurd hmem h2⟩
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- **`idxSet e i ⊆ idxSet e j ↔ Yc P i ⊆ Yc P j`.** The `Δ = Set.univ`/`Yc P i ⊆ U.master`
simplification of `transfer_subset_iff_idxYc`, matching `Theorem88a.lean`'s `embed_subset_iff`. -/
theorem embed_subset_iff_code (i j : ℕ) : idxSet (e P) i ⊆ idxSet (e P) j ↔ Yc P i ⊆ Yc P j := by
  have := transfer_subset_iff_idxYc P i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at this

theorem embed_eq_iff_code (i j : ℕ) : idxSet (e P) i = idxSet (e P) j ↔ Yc P i = Yc P j :=
  ⟨fun h => Set.Subset.antisymm ((embed_subset_iff_code P i j).mp h.subset)
      ((embed_subset_iff_code P j i).mp h.symm.subset),
    fun h => Set.Subset.antisymm ((embed_subset_iff_code P i j).mpr h.subset)
      ((embed_subset_iff_code P j i).mpr h.symm.subset)⟩

/-- **`e P i = e P j ↔ Yc P i = Yc P j`**, the raw-level analogue of `Theorem88a.lean`'s
`embed_eq_iff`. -/
theorem embed_eq_iff_raw_code (i j : ℕ) : e P i = e P j ↔ Yc P i = Yc P j := by
  rw [← idxSet_eq_iff (e P) i j]
  exact embed_eq_iff_code P i j

/-- **`e P i ⊆ e P j ↔ Yc P i ⊆ Yc P j`**, the raw-level analogue of `Theorem88a.lean`'s
`embed_subset_iff`, built from the idxSet-level `embed_subset_iff_code` via `idxSet_subset_iff`. -/
theorem embed_subset_iff_raw_code (i j : ℕ) : e P i ⊆ e P j ↔ Yc P i ⊆ Yc P j := by
  rw [← idxSet_subset_iff (e P) i j]
  exact embed_subset_iff_code P i j

/-- **`∃ k, Yc P k ⊆ Yc P i ∩ Yc P j` is recursively decidable in `(i, j)`.** Transfers
(`embed_subset_iff_raw_code`, twice) to `∃ k, e P k ⊆ e P i ∧ e P k ⊆ e P j`, which is literally
`(P0 P).cons_computable`'s own predicate. -/
theorem DprimeUCode_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yc P k ⊆ Yc P i ∩ Yc P j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff_raw_code P k t.unpair.1, ← embed_subset_iff_raw_code P k t.unpair.2])

theorem transfer_inter_eq_iff_idxYc (i j k : ℕ) :
    idxSet (e P) i ∩ idxSet (e P) j = idxSet (e P) k ↔ Yc P i ∩ Yc P j = Yc P k := by
  have h1 : idxSet (e P) k ⊆ idxSet (e P) i ↔ Yc P k ⊆ Yc P i := embed_subset_iff_code P k i
  have h2 : idxSet (e P) k ⊆ idxSet (e P) j ↔ Yc P k ⊆ Yc P j := embed_subset_iff_code P k j
  have h3 : idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k ↔
      Yc P i ∩ Yc P j ⊆ Yc P k := by
    have := transfer_double_subset_iff_idxYc P i j k
    rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at this
  constructor
  · intro heq
    have hki : idxSet (e P) k ⊆ idxSet (e P) i := heq ▸ Set.inter_subset_left
    have hkj : idxSet (e P) k ⊆ idxSet (e P) j := heq ▸ Set.inter_subset_right
    have hijk : idxSet (e P) i ∩ idxSet (e P) j ⊆ idxSet (e P) k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : Yc P k ⊆ Yc P i := by rw [← heq]; exact Set.inter_subset_left
    have hkj : Yc P k ⊆ Yc P j := by rw [← heq]; exact Set.inter_subset_right
    have hijk : Yc P i ∩ Yc P j ⊆ Yc P k := by rw [heq]
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-- **`Yc P i ∩ Yc P j = Yc P k` is recursively decidable in `(i, j, k)`.** Transfers
(`transfer_inter_eq_iff_idxYc`) to the `idxSet`-level equation, which `idxSet_inter_eq_iff_DAtom`
reduces to two `incl_computable` queries and one `DAtom_recDecidable` query. -/
theorem DprimeUCode_interEq_computable :
    RecDecidable₃ (fun i j k => Yc P i ∩ Yc P j = Yc P k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable_code P |>.and (inclK_j_recDecidable_code P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff_idxYc P t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2,
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

/-- **The intersection index transfers.** `(P0 P).inter n m` (Scott's own primitive-recursive
intersection index for `D`, reused verbatim) also indexes `Yc P n ∩ Yc P m` whenever that
intersection is consistent. -/
theorem DprimeUCode_inter_spec {n m : ℕ} (h : ∃ k, Yc P k ⊆ Yc P n ∩ Yc P m) :
    Yc P ((P0 P).inter n m) = Yc P n ∩ Yc P m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff_raw_code P k n).mpr hk.1)
      ((embed_subset_iff_raw_code P k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff_idxYc P n m ((P0 P).inter n m)).mp hidx).symm

theorem exists_inter_index_of_dmem_code {i j : ℕ} (hDij : D.mem (e P i ∩ e P j)) :
    ∃ m, e P i ∩ e P j = e P m ∧ Yc P i ∩ Yc P j = Yc P m := by
  obtain ⟨m, hm⟩ := (hcover P (e P i ∩ e P j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff_idxYc P i j m).mp (idxSet_inter_of_inter_eq (e P) hm)⟩

/-- **`D'' := DprimeUCode`**: the neighbourhood system generated by `{Yc P n ∣ n ∈ ℕ}`, genuinely
code-driven (`Yc P n = UX (YseqCode P n)`), mirroring `Theorem88a.lean`'s `DprimeU` construction. -/
noncomputable def DprimeUCode : NeighborhoodSystem ℚ where
  mem Y := ∃ n, Y = Yc P n
  master := U.master
  master_nonempty := U.master_nonempty
  master_mem := ⟨0, (Yc_zero_eq_master P).symm⟩
  sub_master := by rintro Y ⟨n, rfl⟩; exact Yc_subset_master P n
  inter_mem := by
    rintro X Y Z ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ hZsub
    have h1 : e P k ⊆ e P i := (embed_subset_iff_raw_code P k i).mpr (hZsub.trans Set.inter_subset_left)
    have h2 : e P k ⊆ e P j := (embed_subset_iff_raw_code P k j).mpr (hZsub.trans Set.inter_subset_right)
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_dmem_code P
      (D.inter_mem (D_mem_e D (e P) (hcover P) i) (D_mem_e D (e P) (hcover P) j)
        (D_mem_e D (e P) (hcover P) k) (Set.subset_inter h1 h2))
    exact ⟨m, hYeq⟩

/-- **Theorem 8.8(b)(vii)(3), presentation half.** `D''` (`DprimeUCode P`, genuinely code-driven:
`X n := Yc P n = UX (YseqCode P n)`) is effectively given, with master index `0`. Its two index
relations and intersection index are reused **unchanged** from `P0 P`; only the carrier family
changed from `Yidx (e P)` (Part 6's classical choice-built sets) to `Yc P` (this file's
`Nat.Primrec`-tracked codes). -/
noncomputable def DprimeUCodePresentation : ComputablePresentation (DprimeUCode P) where
  X n := Yc P n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeUCode_interEq_computable P
  cons_computable := DprimeUCode_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeUCode_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yc_zero_eq_master P

theorem exists_inter_index_of_nonempty_code {i j : ℕ} (hne : (Yc P i ∩ Yc P j).Nonempty) :
    ∃ m, e P i ∩ e P j = e P m ∧ Yc P i ∩ Yc P j = Yc P m := by
  have hne' : (idxSet (e P) i ∩ idxSet (e P) j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff_idxYc P i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yc_subset_master P i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem_code P
    (D.inter_mem (D_mem_e D (e P) (hcover P) i) (D_mem_e D (e P) (hcover P) j)
      (D_mem_e D (e P) (hcover P) k) (Set.subset_inter hki hkj))

/-- **`D'' ◁ U`.** -/
theorem DprimeUCode_subsystem : DprimeUCode P ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact (U_mem_UX (YseqCode P n))
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty_code P hUmem.2.1
    exact ⟨m, hYeq⟩

/-- **Pullback**: the `D`-filter induced by a `D''`-filter `y`. -/
def toDCode (y : (DprimeUCode P).Element) : D.Element where
  mem S := ∃ n, S = e P n ∧ y.mem (Yc P n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D (e P) (hcover P) n
  master_mem := ⟨0, (he0 P).symm, by rw [Yc_zero_eq_master P]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeUCode P).mem (Yc P i ∩ Yc P j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty_code P
      ((DprimeUCode_subsystem P).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover P T).mp hDT
    have hYij : Yc P i ⊆ Yc P j := (embed_subset_iff_raw_code P i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

/-- **Pushforward**: the `D''`-filter induced by a `D`-filter `x`. -/
def toDprimeUCode (x : D.Element) : (DprimeUCode P).Element where
  mem Y := ∃ n, Y = Yc P n ∧ x.mem (e P n)
  sub := fun ⟨n, hn, _⟩ => ⟨n, hn⟩
  master_mem := ⟨0, (Yc_zero_eq_master P).symm, by rw [he0 P]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hem, hYeq⟩ :=
      exists_inter_index_of_dmem_code P (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hYeq, hem ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl⟩ hXY
    have heij : e P i ⊆ e P j := (embed_subset_iff_raw_code P i j).mpr hXY
    exact ⟨j, rfl, x.up_mem hxi (D_mem_e D (e P) (hcover P) j) heij⟩

/-- **The order isomorphism `D.Element ≃o D''.Element`.** -/
noncomputable def domainIsoCode : DomainIso D (DprimeUCode P) where
  toFun := toDprimeUCode P
  invFun := toDCode P
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff_raw_code P n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover P S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff_raw_code P n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover P S).mp (x.sub hxS)
      have hxn : x.mem (e P n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeUCode P x).mem (Yc P n))
      rw [hn, (embed_eq_iff_raw_code P n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

/-- **Theorem 8.8(b)(vii)(3), full statement.** `D''` is effectively given, `D ≅ᴰ D''`, and
`D'' ◁ U`. -/
theorem DprimeUCode_isEffectivelyGiven : (DprimeUCode P).IsEffectivelyGiven :=
  ⟨DprimeUCodePresentation P⟩

/-- **Theorem 8.8(b)(vii)(3), isomorphism half.** `D ≅ᴰ D''`. -/
theorem isomorphic_DprimeUCode : D ≅ᴰ DprimeUCode P := ⟨domainIsoCode P⟩

/-- **The injection `i : D'' → U` is computable.** `i`'s relation `Yc P n \, i \, UX m` reduces to
the raw code-level subset test `UX (YseqCode P n) ⊆ UX m`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the first argument. -/
theorem DprimeUCode_inj_isComputableMap :
    ComputableMap (DprimeUCodePresentation P) UComputablePresentation
      (DprimeUCode_subsystem P).inj := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (YseqCode P t.unpair.1) t.unpair.2) :=
    Nat.Primrec.pair ((primrec_YseqCode P).comp Nat.Primrec.left) Nat.Primrec.right
  have hp : RecDecidable (fun t : ℕ => UX (YseqCode P t.unpair.1) ⊆ UX t.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).inj.rel (Yc P t.unpair.1) (UX t.unpair.2) ↔ _
  rw [Subsystem.inj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨⟨t.unpair.1, rfl⟩, U_mem_UX _, hsub⟩⟩

/-- **The projection `j : U → D''` is computable.** `j`'s relation `UX m \, j \, Yc P n` reduces to
the raw code-level subset test `UX m ⊆ UX (YseqCode P n)`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the second argument. -/
theorem DprimeUCode_proj_isComputableMap :
    ComputableMap UComputablePresentation (DprimeUCodePresentation P)
      (DprimeUCode_subsystem P).proj := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (YseqCode P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((primrec_YseqCode P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => UX t.unpair.1 ⊆ UX (YseqCode P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).proj.rel (UX t.unpair.1) (Yc P t.unpair.2) ↔ _
  rw [Subsystem.proj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨U_mem_UX _, ⟨t.unpair.2, rfl⟩, hsub⟩⟩

/-- **Theorem 8.8(b)(vii)(4), full statement.** The projection pair witnessing `D'' ◁ U` (Proposition
6.12, applied to `DprimeUCode_subsystem P : DprimeUCode P ◁ U`) is computable in both directions
relative to `D''`'s own presentation (`DprimeUCodePresentation`) and `U`'s presentation
(`UComputablePresentation`) — the headline claim of Theorem 8.8(b)(vii). -/
theorem DprimeUCode_projectionPair_isComputable :
    ComputableMap (DprimeUCodePresentation P) UComputablePresentation
        (DprimeUCode_subsystem P).inj ∧
      ComputableMap UComputablePresentation (DprimeUCodePresentation P)
        (DprimeUCode_subsystem P).proj :=
  ⟨DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

end

section
open NeighborhoodSystem Domain.Recursive

/-- **Theorem 8.8(b) (Scott 1981, PRG-19), final assembly.** If `D` is effectively given (via a
`ComputablePresentation P`), the general universality of `U` (Theorem 8.8(a)) can be witnessed by a
`D' : NeighborhoodSystem ℚ` that is *itself* effectively given (`P' : ComputablePresentation D'`),
isomorphic to `D`, a subsystem of `U`, **and** whose projection pair `i := (D' ◁ U).inj`,
`j := (D' ◁ U).proj` (Proposition 6.12) is computable in both directions relative to `P'` and `U`'s
own presentation `UComputablePresentation`. -/
theorem theorem_8_8_b {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D) :
    ∃ (D' : NeighborhoodSystem ℚ) (P' : ComputablePresentation D') (h : D' ◁ U),
      (D ≅ᴰ D') ∧
        ComputableMap P' UComputablePresentation h.inj ∧
        ComputableMap UComputablePresentation P' h.proj :=
  ⟨DprimeUCode P, DprimeUCodePresentation P, DprimeUCode_subsystem P,
    isomorphic_DprimeUCode P, DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 8.8(c), Part 6 of 6 — final assembly.** A computable approximable self-map `a` of an
effectively given `V` (via `P`) makes `fixedNbhd a` effectively given: package Parts 1–5's `D_X`/
`D_inter` enumeration, instantiated at concrete witnesses `qChar` (Part 1) and `cons` (`P`'s own
`cons_computable`), into a `ComputablePresentation (fixedNbhd a)`. -/
theorem fixedNbhd_isEffectivelyGiven {P : ComputablePresentation V} {a : ApproximableMap V V}
    (hcomp : ComputableMap P P a) : (fixedNbhd a).IsEffectivelyGiven := by
  obtain ⟨qChar, hqCharp, hqChar⟩ := diagFixed_exists_qChar hcomp
  obtain ⟨cons, hconsp, hconse⟩ := P.cons_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have h := hconse (Nat.pair n m)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    exact h.symm
  refine ⟨{
    X := D_X P qChar cons
    mem_X := D_X_mem hqChar hcons
    surj := fun hY => D_X_surj hqChar hcons hY
    interEq_computable := D_X_interEq_computable P qChar cons hqCharp hconsp
    cons_computable := D_X_cons_computable P qChar cons hqChar hcons hqCharp hconsp
    inter := D_inter
    inter_primrec := D_inter_primrec
    inter_spec := fun h => D_X_inter_spec hcons h
    masterIdx := 0
    masterIdx_spec := ?_ }⟩
  show D_X P qChar cons 0 = V.master
  show P.X (myFoldCode P qChar cons 0) = V.master
  rw [myFoldCode_eq, decodeList_zero, myFold_nil, P.masterIdx_spec]

/-- **Theorem 8.8(c) (Scott 1981, PRG-19), headline.** If `a : U → U` is a computable, finitary
projection of the universal domain, then `{Y ∈ U ∣ Y a Y}` is effectively given (and, unconditionally
by Theorem 8.5, a subsystem of `U`). As in Theorem 8.6(c)'s converse, `hfin` is carried in the
signature to match Scott's stated hypothesis on `a`, but is **not** actually needed by this
implication — only `hcomp` drives the effectiveness argument; this is called out here rather than
silently dropping the hypothesis. -/
theorem theorem_8_8_c {a : ApproximableMap U U} (_hfin : FinitaryProjection a)
    (hcomp : ComputableMap UComputablePresentation UComputablePresentation a) :
    (fixedNbhd a).IsEffectivelyGiven ∧ fixedNbhd a ◁ U :=
  ⟨fixedNbhd_isEffectivelyGiven hcomp, fixedNbhd_subsystem a⟩

end
section
open NeighborhoodSystem ApproximableMap Exercise326

/-- Every `𝒰`-neighbourhood is non-empty (built into Definition 8.7). -/
theorem U_mem_nonempty : ∀ X, U.mem X → X.Nonempty := fun _ hX => hX.2.1

/-- `𝒰 → 𝒰` is effectively given (Theorem 7.5, applied to `U`'s own presentation twice). -/
theorem funSpaceUU_isEffectivelyGiven : (funSpace U U).IsEffectivelyGiven :=
  funSpace_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 → 𝒰`. -/
noncomputable def funSpaceUUPresentation : ComputablePresentation (funSpace U U) :=
  funSpaceUU_isEffectivelyGiven.some

/-- **`λf. b∘f∘a : (𝒰→𝒰) → (𝒰→𝒰)`**, uncurried as `b ∘ eval ∘ (id ×ₘ a)`. -/
noncomputable def lamComb (a b : ApproximableMap U U) :
    ApproximableMap (funSpace U U) (funSpace U U) :=
  curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a)))

/-- `𝒰 × 𝒰` is effectively given (Theorem 7.4, applied to `U`'s own presentation twice). -/
theorem prodUU_isEffectivelyGiven : (prod U U).IsEffectivelyGiven :=
  prod_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 × 𝒰`. -/
noncomputable def prodUUPresentation : ComputablePresentation (prod U U) :=
  prodUU_isEffectivelyGiven.some

/-- `𝒰 + 𝒰` is effectively given (Theorem 7.4, applied to `U`'s own presentation twice). -/
theorem sumUU_isEffectivelyGiven :
    (sum U U U_mem_nonempty U_mem_nonempty).IsEffectivelyGiven :=
  sum_isEffectivelyGiven U_isEffectivelyGiven U_isEffectivelyGiven

/-- A fixed presentation of `𝒰 + 𝒰`. -/
noncomputable def sumUUPresentation : ComputablePresentation (sum U U U_mem_nonempty U_mem_nonempty) :=
  sumUU_isEffectivelyGiven.some

end



section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`isoInj : D → D''`**, Theorem 2.7 applied to `domainIsoCode P`. -/
noncomputable def isoInj : ApproximableMap D (DprimeUCode P) := ofIso (domainIsoCode P)

/-- **`isoProj : D'' → D`**, Theorem 2.7 applied to the inverse iso. -/
noncomputable def isoProj : ApproximableMap (DprimeUCode P) D := ofIso (domainIsoCode P).symm

/-- `isoInj ∘ isoProj = I_D''`. -/
theorem isoInj_comp_isoProj : (isoInj P).comp (isoProj P) = idMap (DprimeUCode P) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (isoInj P).toElementMap ((isoProj P).toElementMap y) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
    toElementMap_idMap]

/-- **`isoInj`'s relation at raw indices reduces to a single reindexed inclusion.** `n := b` is always
a valid witness (`Yc P b = Yc P b`), and any *other* witness `n` with `Yc P b = Yc P n` forces
`e P b = e P n` (`embed_eq_iff_raw_code`), so it gives no new information. -/
theorem isoInj_rel_iff_incl {a b : ℕ} :
    (isoInj P).rel (P.X a) (Yc P b) ↔ P.X a ⊆ P.X (eIdx P b) := by
  show (∃ _ : D.mem (P.X a), (toDprimeUCode P (D.principal (P.mem_X a))).mem (Yc P b)) ↔ _
  simp only [toDprimeUCode, mem_principal]
  have hb : e P b = P.X (eIdx P b) := rfl
  constructor
  · rintro ⟨-, n, hn, -, hsub⟩
    rwa [← hb, (embed_eq_iff_raw_code P b n).mpr hn]
  · intro hsub
    exact ⟨P.mem_X a, b, rfl, (P0 P).mem_X b, hb ▸ hsub⟩

/-- **`isoInj` is computable** relative to `P`/`DprimeUCodePresentation P`: its raw-index relation is
`incl_computable` reindexed by the primitive-recursive `eIdx P` in the second argument. -/
theorem isoInj_isComputableMap : ComputableMap P (DprimeUCodePresentation P) (isoInj P) := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => P.X t.unpair.1 ⊆ P.X (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (P.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoInj P).rel (P.X t.unpair.1) ((DprimeUCodePresentation P).X t.unpair.2) ↔ _
  exact isoInj_rel_iff_incl P

/-- `isoProj ∘ isoInj = I_D` (Theorem 2.7's `toElementMap_ofIso`, both ways, plus `OrderIso.symm_apply_apply`). -/
theorem isoProj_comp_isoInj : (isoProj P).comp (isoInj P) = idMap D := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (isoProj P).toElementMap ((isoInj P).toElementMap x) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
    toElementMap_idMap]

/-- **`isoProj`'s relation at raw indices reduces to a single reindexed inclusion.** `m := eIdx P a`
is always a valid witness (`e P (eIdx P a) = P.X a` by involutivity), and any *other* witness `m`
with `P.X a = e P m` forces `Yc P (eIdx P a) = Yc P m` (via `embed_eq_iff_raw_code` and
`eIdx_involutive`), so it gives no new information. -/
theorem isoProj_rel_iff_incl {b a : ℕ} :
    (isoProj P).rel (Yc P b) (P.X a) ↔ Yc P b ⊆ Yc P (eIdx P a) := by
  show (∃ _ : (DprimeUCode P).mem (Yc P b),
      (toDCode P ((DprimeUCode P).principal ⟨b, rfl⟩)).mem (P.X a)) ↔ _
  simp only [toDCode]
  have hea : e P (eIdx P a) = P.X a := by
    show P.X (eIdx P (eIdx P a)) = P.X a
    rw [eIdx_involutive P a]
  constructor
  · rintro ⟨-, m, hm, -, hsub⟩
    have heq : e P (eIdx P a) = e P m := hea.trans hm
    rw [(embed_eq_iff_raw_code P (eIdx P a) m).mp heq]
    exact hsub
  · intro hsub
    exact ⟨⟨b, rfl⟩, eIdx P a, hea.symm, ⟨eIdx P a, rfl⟩, hsub⟩

/-- **`isoProj` is computable** relative to `DprimeUCodePresentation P`/`P`: its raw-index relation is
`DprimeUCodePresentation`'s `incl_computable` reindexed by `eIdx P` in the second argument. -/
theorem isoProj_isComputableMap : ComputableMap (DprimeUCodePresentation P) P (isoProj P) := by
  constructor
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => Yc P t.unpair.1 ⊆ Yc P (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((DprimeUCodePresentation P).incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoProj P).rel ((DprimeUCodePresentation P).X t.unpair.1) (P.X t.unpair.2) ↔ _
  exact isoProj_rel_iff_incl P

/-- **`theorem_8_8_b`, strengthened.** For any effectively given `D` (via `P`), there is a
*single* computable projection pair `i : D → U`, `j : U → D` directly (no intermediate isomorphic
copy): compose `isoInj`/`isoProj` (the code-level iso, computable) with `DprimeUCode`'s own projection pair
into `U` (Theorem 8.8(b)(vii), computable). -/
theorem theorem_8_8_b_strong :
    ∃ (i : ApproximableMap D U) (j : ApproximableMap U D),
      j.comp i = idMap D ∧ i.comp j ≤ idMap U ∧
        ComputableMap P UComputablePresentation i ∧
        ComputableMap UComputablePresentation P j := by
  set h := DprimeUCode_subsystem P with hh
  refine ⟨h.inj.comp (isoInj P), (isoProj P).comp h.proj, ?_, ?_, ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc h.proj h.inj (isoInj P), h.proj_comp_inj, idMap_comp]
    exact isoProj_comp_isoInj P
  · have heq : (h.inj.comp (isoInj P)).comp ((isoProj P).comp h.proj) = h.inj.comp h.proj := by
      rw [comp_assoc, ← comp_assoc (isoInj P) (isoProj P) h.proj, isoInj_comp_isoProj, idMap_comp]
    rw [heq]
    exact h.inj_comp_proj_le
  · exact comp_isComputable (isoInj_isComputableMap P) (DprimeUCode_inj_isComputableMap P)
  · exact comp_isComputable (DprimeUCode_proj_isComputableMap P) (isoProj_isComputableMap P)

end

end DomainTheory.NeighbourhoodSystems
end
