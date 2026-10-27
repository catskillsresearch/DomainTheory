module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive


/- concordance: source L5161 EXERCISE 8.15 — QFuel / TreeVal / Q'X -/

/-- One fuel-recursion step for evaluating a term-algebra code: tag `0` (`leaf j`) applies `r` to
the payload; tag `1` (`node t1 t2`) combines the two (previous-fuel-level) recursive values via
`Uinter`; any other tag (`master`, or junk) falls back to `𝒰`'s master index. Mirrors
`decodeFuelOkCharBody`'s tag-dispatch shape exactly. -/
def QBody (r : ℕ → ℕ) (prev : ℕ → ℕ) (c : ℕ) : ℕ :=
  selectFn (isOne (1 - c.unpair.1)) (r c.unpair.2)
    (selectFn (isOne (2 - c.unpair.1))
      (Uinter (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2))
      UComputablePresentation.masterIdx)


/-- `QBody`'s value at `c` depends on `prev` only through its values at `c`'s two (`Nat.unpair`)
children — the locality fact needed to bridge two different `prev`s that merely *agree* there. -/
theorem QBody_local (r : ℕ → ℕ) (f g : ℕ → ℕ) (c : ℕ)
    (h1 : f c.unpair.2.unpair.1 = g c.unpair.2.unpair.1)
    (h2 : f c.unpair.2.unpair.2 = g c.unpair.2.unpair.2) :
    QBody r f c = QBody r g c := by
  unfold QBody
  rw [h1, h2]


/-- `QFuel r fuel c`: fuel-indexed evaluation of a term-algebra code (base value `0` at `fuel = 0`,
irrelevant since every use below supplies `fuel > c`). -/
def QFuel (r : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c => QBody r (QFuel r fuel) c


/-- `QBody`'s step with `prev` replaced by table lookup (`fuelTable`'s calling convention). -/
def QLookup (r : ℕ → ℕ) (w : ℕ) : ℕ := QBody r (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2


theorem QFuel_fuelTable_eq (r : ℕ → ℕ) :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable (QLookup r) bound fuel) c 0 = QFuel r fuel c :=
  fuelTable_eq_of_recursion (F := QFuel r) (Body := QBody r) (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold QLookup QBody; simp only [unpair_pair_fst, unpair_pair_snd])
    (fun f g c h => QBody_local r f g c
      (h c.unpair.2.unpair.1 (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)))
      (h c.unpair.2.unpair.2 (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c))))


/-- `foldCode`'s per-step function for `Q'X`: combine the running accumulator with `r` applied to
the next list entry. Packaged in `foldCode`'s `pair x (pair acc params)` calling convention
(`params` unused). -/
def QstepFn (r : ℕ → ℕ) (t : ℕ) : ℕ := Uinter t.unpair.2.unpair.1 (r t.unpair.1)


/-- The raw `U`-index computed by folding `Uinter ∘ r` over the list coded by `n`, starting from
`U`'s master index. -/
def Q'Xcode (r : ℕ → ℕ) (n : ℕ) : ℕ :=
  foldCode (QstepFn r) 0 UComputablePresentation.masterIdx n


/-- **`Q'X r`: the candidate enumeration of `D'x`'s neighbourhoods.** -/
def Q'X (r : ℕ → ℕ) (n : ℕ) : Set ℚ := UX (Q'Xcode r n)


/-- `Q'X r n` is `UX` at the `idxchain`-index of the `r`-image of `n`'s list — i.e. `Q'X r` really is
`Theorem75`'s generic `idxchain` fold, just specialized through `r`. -/
theorem Q'X_eq (r : ℕ → ℕ) (n : ℕ) :
    Q'X r n = UX (idxchain UComputablePresentation (List.map r (decodeList n))) := by
  have hstep : (fun (acc x : ℕ) => QstepFn r (Nat.pair x (Nat.pair acc 0)))
      = fun acc x => Uinter acc (r x) := by
    funext acc x; unfold QstepFn; simp only [unpair_pair_fst, unpair_pair_snd]
  unfold Q'X Q'Xcode idxchain
  rw [foldCode_eq', hstep, List.foldl_map]
  rfl


/-- **`TreeVal r c`: the fuel-free evaluator** (fuel `c + 1` is always enough, `c` being an upper
bound on any code's own recursion depth). -/
def TreeVal (r : ℕ → ℕ) (c : ℕ) : ℕ := QFuel r (c + 1) c


/-- **Tag-`0` unfolding, for an arbitrary code (not just a literal `leafCode`).** Needed for the
`mem_X` induction below, which case-splits on an arbitrary code's tag rather than reconstructing it
as `leafCode`/`nodeCode`/`masterCode`. -/
theorem TreeVal_of_tag0 (r : ℕ → ℕ) {c : ℕ} (h : c.unpair.1 = 0) : TreeVal r c = r c.unpair.2 := by
  have h1 : isOne (1 - c.unpair.1) = 1 := by rw [h]; rfl
  show QBody r (QFuel r c) c = r c.unpair.2
  unfold QBody
  simp only [h1, selectFn_one]


/-- **Tag-`≥ 2` unfolding, for an arbitrary code.** -/
theorem TreeVal_of_tag_ge2 (r : ℕ → ℕ) {c : ℕ} (h : 2 ≤ c.unpair.1) :
    TreeVal r c = UComputablePresentation.masterIdx := by
  have h1 : isOne (1 - c.unpair.1) = 0 := by
    have : (1 - c.unpair.1 : ℕ) = 0 := by omega
    rw [this]; rfl
  have h2 : isOne (2 - c.unpair.1) = 0 := by
    have : (2 - c.unpair.1 : ℕ) = 0 := by omega
    rw [this]; rfl
  show QBody r (QFuel r c) c = UComputablePresentation.masterIdx
  unfold QBody
  simp only [h1, h2, selectFn_zero]


/-- **`Uinter`'s unconditional dichotomy.** Unlike a generic `ComputablePresentation.inter` (whose
behaviour off the consistent domain is unspecified "junk"), `𝒰`'s canonicalizing `Uinter` always
produces *either* the true intersection *or* falls back to `U.master` — `canonList`'s documented
"fall back to `(0,1)` if nothing survives" behaviour, holding **unconditionally** (no consistency
hypothesis needed). This is the key fact an abstract `ComputablePresentation` cannot supply. -/
theorem UX_Uinter_dichotomy (n m : ℕ) :
    UX (Uinter n m) = U.master ∨ UX (Uinter n m) = UX n ∩ UX m := by
  have hUXeq : UX (Uinter n m) = presentedIntervals (canonList (decodeQPairList (Uinter n m))) :=
    UX_eq (Uinter n m)
  have hL : presentedIntervals (decodeQPairList (Uinter n m)) = UX n ∩ UX m := by
    show presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))
        = UX n ∩ UX m
    rw [presentedIntervals_decodeQPairList_combineCode]
    rfl
  rcases hfilt : ((decodeQPairList (Uinter n m)).map qpClip).filter
      (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · left
    rw [hUXeq, canonList_eq_of_filter_eq_nil hfilt, presentedIntervals_singleton_zero_one]
  · right
    rw [hUXeq, canonList_eq_of_filter_eq_cons hfilt, ← hfilt, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, hL]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact Set.inter_eq_left.mpr (Set.inter_subset_left.trans hsubn)


/-- **List-level choice, choice-free.** If every entry of `l` has an `r`-preimage, `l` itself is the
`r`-image of some list — built by ordinary list induction (`Exists.elim` inside a `Prop`-valued goal
at each step), not `Classical.choice`. -/
theorem exists_preimage_of_forall_mem {r : ℕ → ℕ} {l : List ℕ} (h : ∀ i ∈ l, ∃ n, r n = i) :
    ∃ l0 : List ℕ, l0.map r = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons i l' ih =>
    obtain ⟨n0, hn0⟩ := h i List.mem_cons_self
    obtain ⟨l0', hl0'⟩ := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    exact ⟨n0 :: l0', by simp [hn0, hl0']⟩


/-- `leaf j`: the term-algebra code evaluating to `r j`. -/
def leafCode (j : ℕ) : ℕ := Nat.pair 0 j


/-- **Unfolding at a leaf.** -/
theorem TreeVal_leaf (r : ℕ → ℕ) (j : ℕ) : TreeVal r (leafCode j) = r j := by
  have htag : (leafCode j).unpair.1 = 0 := by unfold leafCode; rw [unpair_pair_fst]
  have hpay : (leafCode j).unpair.2 = j := by unfold leafCode; rw [unpair_pair_snd]
  have h1 : isOne (1 - (leafCode j).unpair.1) = 1 := by rw [htag]; rfl
  show QBody r (QFuel r (leafCode j)) (leafCode j) = r j
  unfold QBody
  simp only [h1, hpay, selectFn_one]


/-- `master`: the term-algebra code evaluating to `𝒰`'s master index. -/
def masterCode : ℕ := Nat.pair 2 0


/-- **Unfolding at the master constant.** -/
theorem TreeVal_master (r : ℕ → ℕ) : TreeVal r masterCode = UComputablePresentation.masterIdx := by
  have htag : masterCode.unpair.1 = 2 := by unfold masterCode; rw [unpair_pair_fst]
  have h1 : isOne (1 - masterCode.unpair.1) = 0 := by rw [htag]; rfl
  have h2 : isOne (2 - masterCode.unpair.1) = 0 := by rw [htag]; rfl
  show QBody r (QFuel r masterCode) masterCode = UComputablePresentation.masterIdx
  unfold QBody
  simp only [h1, h2, selectFn_zero]


/-- `node t1 t2`: the term-algebra code evaluating to `Uinter (val t1) (val t2)`. -/
def nodeCode (t1 t2 : ℕ) : ℕ := Nat.pair 1 (Nat.pair t1 t2)


theorem primrec_QLookup (r : ℕ → ℕ) (hr : Nat.Primrec r) : Nat.Primrec (QLookup r) := by
  have hleaf : Nat.Primrec (fun w : ℕ => r w.unpair.2.unpair.2) :=
    hr.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hleft : Nat.Primrec (fun w : ℕ => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0) :=
    (primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (Nat.Primrec.const 0)))).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hright : Nat.Primrec (fun w : ℕ => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    (primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (Nat.Primrec.const 0)))).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnode : Nat.Primrec (fun w : ℕ =>
      Uinter (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0)
        (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0)) :=
    (Uinter_primrec.comp (hleft.pair hright)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have htag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hisone1 : Nat.Primrec (fun w : ℕ => isOne (1 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have hisone2 : Nat.Primrec (fun w : ℕ => isOne (2 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  refine (primrec_selectFn hisone1 hleaf
    (primrec_selectFn hisone2 hnode (Nat.Primrec.const UComputablePresentation.masterIdx))).of_eq
    fun w => ?_
  show _ = QLookup r w
  unfold QLookup QBody
  match tag : w.unpair.2.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01' : (1 - 1 : ℕ) = 0 := rfl
    have h12' : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01', h12', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 2 =>
    have h01' : (1 - (t + 2) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - (t + 2) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [h01', h12', isOne_zero, selectFn_zero]


/-- **`QFuel r` is jointly primitive recursive in `(fuel, code)`.** Mirrors
`primrec_decodeFuelOkChar2` exactly. -/
theorem primrec_QFuel2 (r : ℕ → ℕ) (hr : Nat.Primrec r) :
    Nat.Primrec (fun s : ℕ => QFuel r s.unpair.1 s.unpair.2) := by
  have hft := primrec_fuelTable (primrec_QLookup r hr)
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable (QLookup r) s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable (QLookup r) s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (hcomp.pair ((Nat.Primrec.right).pair (Nat.Primrec.const 0)))).of_eq
      fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact hnth.of_eq fun s => QFuel_fuelTable_eq r s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)


theorem primrec_TreeVal (r : ℕ → ℕ) (hr : Nat.Primrec r) : Nat.Primrec (TreeVal r) := by
  have h2 := primrec_QFuel2 r hr
  have hpack : Nat.Primrec (fun c : ℕ => Nat.pair (c + 1) c) :=
    (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)).pair Nat.Primrec.id
  refine (h2.comp hpack).of_eq fun c => ?_
  show QFuel r (Nat.pair (c + 1) c).unpair.1 (Nat.pair (c + 1) c).unpair.2 = TreeVal r c
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl


/-- If `c`'s tag (`c.unpair.1`) is nonzero, `c`'s payload (`c.unpair.2`) is *strictly* smaller than
`c` itself — the key well-foundedness fact driving `nodeCode`'s children being strictly smaller
than the parent (choice-free: only uses the custom `unpair_pair`/`le_pair_right`/
`Nat.pair_lt_pair_left`, all already audited elsewhere in this file). -/
theorem unpair_snd_lt_of_unpair_fst_pos {c : ℕ} (h : 0 < c.unpair.1) : c.unpair.2 < c := by
  have h1 : c.unpair.2 ≤ Nat.pair 0 c.unpair.2 := le_pair_right 0 c.unpair.2
  have h2 : Nat.pair 0 c.unpair.2 < Nat.pair c.unpair.1 c.unpair.2 := Nat.pair_lt_pair_left _ h
  rw [Nat.pair_unpair] at h2
  omega


/-- **Stabilization.** Once the fuel exceeds the code, `QFuel r`'s value no longer depends on
*which* sufficiently-large fuel was supplied — the key fact letting us read off a genuine,
fuel-free evaluator `TreeVal` below. Proved by strong induction on `c`, splitting on whether `c`'s
tag is `0` (no recursion, both sides agree immediately) or positive (both children are strictly
`< c`, via `unpair_snd_lt_of_unpair_fst_pos`, so the induction hypothesis applies to them). -/
theorem QFuel_stable (r : ℕ → ℕ) :
    ∀ c fuel fuel', c < fuel → c < fuel' → QFuel r fuel c = QFuel r fuel' c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro fuel fuel' hfuel hfuel'
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    show QBody r (QFuel r f) c = QBody r (QFuel r f') c
    rcases Nat.eq_zero_or_pos c.unpair.1 with htag0 | htagpos
    · have hval : isOne (1 - c.unpair.1) = 1 := by rw [htag0]; rfl
      unfold QBody
      simp only [hval, selectFn_one]
    · have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos htagpos
      have h1lt : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
      have h2lt : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
      have hfc : c ≤ f := by omega
      have hfc' : c ≤ f' := by omega
      have e1 := ih c.unpair.2.unpair.1 h1lt f f'
        (lt_of_lt_of_le h1lt hfc) (lt_of_lt_of_le h1lt hfc')
      have e2 := ih c.unpair.2.unpair.2 h2lt f f'
        (lt_of_lt_of_le h2lt hfc) (lt_of_lt_of_le h2lt hfc')
      exact QBody_local r (QFuel r f) (QFuel r f') c e1 e2


theorem TreeVal_eq_QFuel (r : ℕ → ℕ) {c fuel : ℕ} (h : c < fuel) : TreeVal r c = QFuel r fuel c :=
  QFuel_stable r c (c + 1) fuel (Nat.lt_succ_self c) h


/-- **Tag-`1` unfolding, for an arbitrary code.** -/
theorem TreeVal_of_tag1 (r : ℕ → ℕ) {c : ℕ} (h : c.unpair.1 = 1) :
    TreeVal r c = Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2) := by
  have h1 : isOne (1 - c.unpair.1) = 0 := by rw [h]; rfl
  have h2 : isOne (2 - c.unpair.1) = 1 := by rw [h]; rfl
  have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos (by omega)
  have ht1 : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
  have ht2 : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
  show QBody r (QFuel r c) c = Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2)
  unfold QBody
  simp only [h1, h2, selectFn_zero, selectFn_one]
  rw [TreeVal_eq_QFuel r ht1, TreeVal_eq_QFuel r ht2]


/-- `nodeCode t1 t2`'s two children are each strictly smaller than the whole code. -/
theorem nodeCode_fst_lt (t1 t2 : ℕ) : t1 < nodeCode t1 t2 := by
  have hpos : 0 < (nodeCode t1 t2).unpair.1 := by
    unfold nodeCode; rw [unpair_pair_fst]; omega
  have hsnd : (nodeCode t1 t2).unpair.2 < nodeCode t1 t2 :=
    unpair_snd_lt_of_unpair_fst_pos hpos
  have ht1 : t1 ≤ (nodeCode t1 t2).unpair.2 := by
    unfold nodeCode; rw [unpair_pair_snd]; exact le_pair_left t1 t2
  omega


theorem nodeCode_snd_lt (t1 t2 : ℕ) : t2 < nodeCode t1 t2 := by
  have hpos : 0 < (nodeCode t1 t2).unpair.1 := by
    unfold nodeCode; rw [unpair_pair_fst]; omega
  have hsnd : (nodeCode t1 t2).unpair.2 < nodeCode t1 t2 :=
    unpair_snd_lt_of_unpair_fst_pos hpos
  have ht2 : t2 ≤ (nodeCode t1 t2).unpair.2 := by
    unfold nodeCode; rw [unpair_pair_snd]; exact le_pair_right t1 t2
  omega


/-- **Unfolding at a node.** -/
theorem TreeVal_node (r : ℕ → ℕ) (t1 t2 : ℕ) :
    TreeVal r (nodeCode t1 t2) = Uinter (TreeVal r t1) (TreeVal r t2) := by
  have ht1 : t1 < nodeCode t1 t2 := nodeCode_fst_lt t1 t2
  have ht2 : t2 < nodeCode t1 t2 := nodeCode_snd_lt t1 t2
  have htag : (nodeCode t1 t2).unpair.1 = 1 := by unfold nodeCode; rw [unpair_pair_fst]
  have hc1 : (nodeCode t1 t2).unpair.2.unpair.1 = t1 := by
    unfold nodeCode; rw [unpair_pair_snd, unpair_pair_fst]
  have hc2 : (nodeCode t1 t2).unpair.2.unpair.2 = t2 := by
    unfold nodeCode; rw [unpair_pair_snd, unpair_pair_snd]
  have h1 : isOne (1 - (nodeCode t1 t2).unpair.1) = 0 := by rw [htag]; rfl
  have h2 : isOne (2 - (nodeCode t1 t2).unpair.1) = 1 := by rw [htag]; rfl
  show QBody r (QFuel r (nodeCode t1 t2)) (nodeCode t1 t2) = Uinter (TreeVal r t1) (TreeVal r t2)
  unfold QBody
  simp only [h1, h2, hc1, hc2, selectFn_zero, selectFn_one]
  rw [TreeVal_eq_QFuel r ht1, TreeVal_eq_QFuel r ht2]


theorem primrec_QstepFn {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (QstepFn r) := by
  unfold QstepFn
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have h2 : Nat.Primrec (fun t : ℕ => r t.unpair.1) := hr.comp Nat.Primrec.left
  exact (Uinter_primrec.comp (h1.pair h2)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]


theorem primrec_Q'Xcode {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (Q'Xcode r) :=
  primrec_foldCode (primrec_QstepFn hr) (Nat.Primrec.const 0)
    (Nat.Primrec.const UComputablePresentation.masterIdx) Nat.Primrec.id

end DomainTheory.NeighbourhoodSystems
