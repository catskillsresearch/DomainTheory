module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/- concordance: source L5161 EXERCISE 8.15 — Q2X / Q'xPresentation -/

/-- **`Q2X r`: the term-algebra enumeration of `D'x`'s neighbourhoods.** -/
def Q2X (c : ℕ) : Set ℚ := UX (TreeVal r c)


/-- **`Q2X r`'s intersection function**: literally the `node` constructor. -/
def Q2inter (c1 c2 : ℕ) : ℕ := nodeCode c1 c2


/-- **`surj` bridge, part 1: embed a `List ℕ` into a term-algebra code.** Left-fold accumulator
mirroring *exactly* the fold shape of `Theorem75.idxchain`/`Q'X` (`Uinter`-folded from the master),
via `nodeCode`/`leafCode` instead of `Uinter`/`r` directly — so that `TreeVal` evaluates it to the
same `U`-index (`TreeVal_listToTreeAux` below). -/
def listToTreeAux : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | acc, j :: l => listToTreeAux (nodeCode acc (leafCode j)) l


theorem primrec_Q2inter : Nat.Primrec (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) := by
  have heq : (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) = fun t => Nat.pair 1 t := by
    funext t; unfold Q2inter nodeCode; rw [pair_unpair]
  rw [heq]
  exact Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.id


/-- **`interEq_computable` for `Q2X r`.** A pure reindexing of `U`'s own `U_interEq_computable`
along the primitive-recursive `TreeVal r` — exactly `ComputablePresentation.reindexInvolutive`'s
`interEq_computable` proof pattern, minus the involution (only needed there for the `masterIdx`/
`inter` fields, not for `.comp`-reindexing a `RecDecidable`). -/
theorem Q2_interEq_computable (hr : Nat.Primrec r) :
    RecDecidable₃ (fun n m k => Q2X r n ∩ Q2X r m = Q2X r k) := by
  have hTV := primrec_TreeVal r hr
  have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (TreeVal r t.unpair.1)
      (Nat.pair (TreeVal r t.unpair.2.unpair.1) (TreeVal r t.unpair.2.unpair.2))) :=
    (hTV.comp Nat.Primrec.left).pair
      ((hTV.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
        (hTV.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine RecDecidable.of_iff (fun t => ?_) (U_interEq_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  rfl


theorem Q2X_masterIdx_spec :
    Q2X r masterCode = (toSubsystemSys UComputablePresentation x).master := by
  show UX (TreeVal r masterCode) = U.master
  rw [TreeVal_master]
  exact UX_UmasterIdx


/-- **`surj` for `Q'X r`.** Every `D'x`-neighbourhood `Y` is some `Q'X r n`: unwind `Y`'s `finGen`
witness `sub`, use `hspec` + `exists_preimage_of_forall_mem` to find a preimage list `sub0` with
`sub0.map r = sub`, and read off `Y` via the *generic* `Theorem75.idxchain_spec` (applicable because
`sub`'s own consistency — `U.mem (interFrom … sub)` — is exactly `hDY` rewritten along `hYeq`). -/
theorem Q'x_surj
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i)
    {Y : Set ℚ} (hY : (toSubsystemSys UComputablePresentation x).mem Y) :
    ∃ n, Q'X r n = Y := by
  obtain ⟨js, hxjs, sub, hsub, hDY, hYeq⟩ := hY
  have hjsmem : ∀ i ∈ js, (toSubsystemSys UComputablePresentation x).mem (UX i) :=
    (mem_nbhdGen_iff UComputablePresentation x js).mp hxjs
  have hsubmem : ∀ i ∈ sub, (toSubsystemSys UComputablePresentation x).mem (UX i) :=
    fun i hi => hjsmem i (hsub.subset hi)
  obtain ⟨sub0, hsub0⟩ := exists_preimage_of_forall_mem (fun i hi => (hspec i).mp (hsubmem i hi))
  refine ⟨encodeList sub0, ?_⟩
  rw [Q'X_eq, decodeList_encodeList, hsub0, hYeq]
  exact idxchain_spec UComputablePresentation (hYeq ▸ hDY)


/-- **`mem_X` for `Q2X r`.** Every `Q2X r c` is a `D'x`-neighbourhood — by strong induction on the
code `c`, splitting on its tag exactly as `TreeVal` itself does: tag `0` (leaf) is
`D'x.mem (UX (r j))`, always true by `hspec` (witness `j` itself); tag `1` (node) combines the two
(inductively already-`D'x.mem`) children via `Uinter`'s dichotomy (`UX_Uinter_dichotomy`), landing on
`D'x.master_mem` on fallback or on `x`'s own filter closure (`nbhdGen_inter`/`interFrom_append_eq`,
exactly as in `toSubsystemSys_mem_foldl_Uinter`) otherwise; tag `≥ 2` (master) is `D'x.master_mem`
directly via `masterIdx_spec`. -/
theorem Q2x_mem_X (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) :
    ∀ c, (toSubsystemSys UComputablePresentation x).mem (Q2X r c) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    show (toSubsystemSys UComputablePresentation x).mem (UX (TreeVal r c))
    rcases Nat.lt_or_ge c.unpair.1 2 with htag | htag
    · have htag01 : c.unpair.1 = 0 ∨ c.unpair.1 = 1 := by omega
      rcases htag01 with htagv | htagv
      · rw [TreeVal_of_tag0 r htagv]
        exact (hspec (r c.unpair.2)).mpr ⟨c.unpair.2, rfl⟩
      · rw [TreeVal_of_tag1 r htagv]
        have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos (by omega)
        have ht1 : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
        have ht2 : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
        have hm1 := ih c.unpair.2.unpair.1 ht1
        have hm2 := ih c.unpair.2.unpair.2 ht2
        unfold Q2X at hm1 hm2
        rcases UX_Uinter_dichotomy (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2)
          with hcase | hcase
        · rw [hcase]; exact (toSubsystemSys UComputablePresentation x).master_mem
        · rw [hcase]
          obtain ⟨jsA, hxA, subA, hsubA, hDA, hAeq⟩ := hm1
          obtain ⟨jsB, hxB, subB, hsubB, hDB, hBeq⟩ := hm2
          have hUmem : U.mem (UX (TreeVal r c.unpair.2.unpair.1) ∩ UX (TreeVal r c.unpair.2.unpair.2)) :=
            hcase ▸ U_mem_UX (Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2))
          refine ⟨jsA ++ jsB, nbhdGen_inter UComputablePresentation jsA jsB ▸ x.inter_mem hxA hxB,
            subA ++ subB, hsubA.append hsubB, hUmem, ?_⟩
          rw [hAeq, hBeq, interFrom_append_eq UComputablePresentation U.master subA subB]
    · rw [TreeVal_of_tag_ge2 r htag]
      show (toSubsystemSys UComputablePresentation x).mem (UX UmasterIdx)
      rw [UX_UmasterIdx]
      exact (toSubsystemSys UComputablePresentation x).master_mem


/-- **`cons_computable` for `Q2X r`.** The crux resolved by the term algebra: the backward
direction's witness is `nodeCode n m`, no search needed to *name* it, and it works because
`Uinter_spec` applies exactly when consistency holds. -/
theorem Q2_cons_computable (hr : Nat.Primrec r) :
    RecDecidable₂ (fun n m => ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) := by
  have hTV := primrec_TreeVal r hr
  have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (TreeVal r t.unpair.1) (TreeVal r t.unpair.2)) :=
    (hTV.comp Nat.Primrec.left).pair (hTV.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) (U_cons_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨TreeVal r k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨nodeCode t.unpair.1 t.unpair.2, ?_⟩
    show UX (TreeVal r (nodeCode t.unpair.1 t.unpair.2)) ⊆
      UX (TreeVal r t.unpair.1) ∩ UX (TreeVal r t.unpair.2)
    rw [TreeVal_node, Uinter_spec ⟨k, hk⟩]


/-- **`inter_spec` for `Q2X r`.** The hypothesis is exactly what `Uinter_spec` needs (a `UX`-witness
of consistency, transported through `TreeVal`), so `nodeCode n m` genuinely indexes the intersection
— no fallback case to worry about. -/
theorem Q2inter_spec {n m : ℕ} (h : ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) :
    Q2X r (Q2inter n m) = Q2X r n ∩ Q2X r m := by
  obtain ⟨k, hk⟩ := h
  show UX (TreeVal r (nodeCode n m)) = UX (TreeVal r n) ∩ UX (TreeVal r m)
  rw [TreeVal_node]
  exact Uinter_spec ⟨TreeVal r k, hk⟩


theorem TreeVal_listToTreeAux (acc : ℕ) (l : List ℕ) :
    TreeVal r (listToTreeAux acc l) = l.foldl (fun a j => Uinter a (r j)) (TreeVal r acc) := by
  induction l generalizing acc with
  | nil => simp [listToTreeAux]
  | cons j l ih =>
    simp only [listToTreeAux, List.foldl_cons]
    rw [ih, TreeVal_node, TreeVal_leaf]


/-- **`surj` for `Q2X r`.** Every `D'x`-neighbourhood `Y` is some `Q2X r c` — reduce to the already-
proven list-based `Q'x_surj` (`Y = Q'X r n` for some `n`), then push `decodeList n` through
`listToTreeAux` and identify the result with `idxchain`'s own fold via `List.foldl_map`, so the same
`n` (repackaged as a tree code) also witnesses `Q2X r`. No fresh combinatorial work: this is a pure
bridging argument between the list-indexed and term-algebra-indexed enumerations of the *same*
underlying `Uinter`-folds. -/
theorem Q2x_surj (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i)
    {Y : Set ℚ} (hY : (toSubsystemSys UComputablePresentation x).mem Y) :
    ∃ c, Q2X r c = Y := by
  obtain ⟨n, hn⟩ := Q'x_surj r x hspec hY
  refine ⟨listToTreeAux masterCode (decodeList n), ?_⟩
  have hcode : (decodeList n).foldl (fun a j => Uinter a (r j)) UComputablePresentation.masterIdx
      = idxchain UComputablePresentation (List.map r (decodeList n)) := by
    unfold idxchain
    rw [List.foldl_map]
    rfl
  show UX (TreeVal r (listToTreeAux masterCode (decodeList n))) = Y
  rw [TreeVal_listToTreeAux, TreeVal_master, hcode, ← Q'X_eq]
  exact hn


/-- **Subgoal 6f, capstone.** `D'x := toSubsystemSys UComputablePresentation x` admits a genuine
`ComputablePresentation`, assembled from `Q2X`/`Q2x_mem_X`/`Q2x_surj`/`Q2_interEq_computable`/
`Q2_cons_computable`/`Q2inter`/`Q2inter_spec`/`masterCode`/`Q2X_masterIdx_spec` — resolving the gap
flagged above via the binary term algebra. -/
def Q'xPresentation (hr : Nat.Primrec r)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) :
    ComputablePresentation (toSubsystemSys UComputablePresentation x) where
  X := Q2X r
  mem_X := Q2x_mem_X r x hspec
  surj := Q2x_surj r x hspec
  interEq_computable := Q2_interEq_computable r hr
  cons_computable := Q2_cons_computable r hr
  inter := Q2inter
  inter_primrec := primrec_Q2inter
  inter_spec := fun h => Q2inter_spec r h
  masterIdx := masterCode
  masterIdx_spec := Q2X_masterIdx_spec r x


/-- **The safe-fold invariant.** Folding `Uinter` from a starting point already in `D'x.mem` along a
list all of whose `UX`-images are also in `D'x.mem` stays in `D'x.mem`: `x`'s own *unconditional*
filter closure (`Element.inter_mem`, via `nbhdGen_inter`) combines the two generators' witnessing
index-lists when `Uinter`'s fold genuinely computes an intersection (dichotomy's right disjunct,
using `interFrom_append_eq`), and `D'x.master_mem` handles the fallback (left disjunct). -/
theorem toSubsystemSys_mem_foldl_Uinter (acc : ℕ)
    (L : List ℕ) (hacc : (toSubsystemSys UComputablePresentation x).mem (UX acc))
    (hL : ∀ i ∈ L, (toSubsystemSys UComputablePresentation x).mem (UX i)) :
    (toSubsystemSys UComputablePresentation x).mem
      (UX (L.foldl (fun a j => Uinter a j) acc)) := by
  induction L generalizing acc with
  | nil => simpa using hacc
  | cons j L' ih =>
    rw [List.forall_mem_cons] at hL
    have hacc' : (toSubsystemSys UComputablePresentation x).mem (UX (Uinter acc j)) := by
      rcases UX_Uinter_dichotomy acc j with hcase | hcase
      · rw [hcase]; exact (toSubsystemSys UComputablePresentation x).master_mem
      · rw [hcase]
        obtain ⟨jsA, hxA, subA, hsubA, hDA, hAeq⟩ := hacc
        obtain ⟨jsJ, hxJ, subJ, hsubJ, hDJ, hJeq⟩ := hL.1
        have hUmem : U.mem (UX acc ∩ UX j) := hcase ▸ U_mem_UX (Uinter acc j)
        refine ⟨jsA ++ jsJ,
          nbhdGen_inter UComputablePresentation jsA jsJ ▸ x.inter_mem hxA hxJ,
          subA ++ subJ, hsubA.append hsubJ, hUmem, ?_⟩
        rw [hAeq, hJeq, interFrom_append_eq UComputablePresentation U.master subA subJ]
    exact ih (Uinter acc j) hacc' hL.2

/-- **`mem_X` for `Q'X r`.** Every `Q'X r n` is a `D'x`-neighbourhood — no consistency hypothesis on
`n` needed, since (a) every entry `r j` of the folded list is *unconditionally* `D'x.mem (UX (r j))`
by `hspec` (taking the trivial witness `j`), and (b) `toSubsystemSys_mem_foldl_Uinter` safely folds
any such list, landing on `D'x.master_mem` if `Uinter`'s dichotomy ever falls back. -/
theorem Q'x_mem_X
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) (n : ℕ) :
    (toSubsystemSys UComputablePresentation x).mem (Q'X r n) := by
  rw [Q'X_eq]
  show (toSubsystemSys UComputablePresentation x).mem
      (UX ((List.map r (decodeList n)).foldl (fun a j => Uinter a j)
        UComputablePresentation.masterIdx))
  apply toSubsystemSys_mem_foldl_Uinter
  · show (toSubsystemSys UComputablePresentation x).mem (UX UmasterIdx)
    rw [UX_UmasterIdx]
    exact (toSubsystemSys UComputablePresentation x).master_mem
  · intro i hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    exact (hspec (r j)).mpr ⟨j, rfl⟩




end DomainTheory.NeighbourhoodSystems
