module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_6
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DiagFixed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.D_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DprimeUPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YseqCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode_more

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26

@[expose] public section

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

theorem Yc_subset_master (n : ℕ) : Yc P n ⊆ U.master := (U_mem_UX (YseqCode P n)).2.2

/-- **`Yc P 0 = U.master`** (Scott's convention `Y₀ = U.master`, matching `Yseq_zero_eq_master`):
the unique bit-source realizing depth `1` with bit `0` set is `k = 1`, whose atom is non-junk
(`idxSet (e P) 0 = Set.univ`, so the "positive" constraint at index `0` is vacuous) and whose code
is literally `UmasterIdx`, since the *negative* sibling constraint (`DAtom (P0 P) [] [0]`) is
already empty — freezing `atomUCode` unchanged through the step (mirrors `atomUCode.subset`'s own
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
    rw [atomUCode.succ, atomUPos_zero, atomUNeg_zero, hbit, selectFn_one]
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
    rw [hnegEmpty, selectFn_one, atomUCode.zero]
  rw [hcode, UX_UmasterIdx]


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
