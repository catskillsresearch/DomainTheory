module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.TreeVal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.TreeVal_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VComputablePresentation

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α}

/- concordance: source L5161 EXERCISE 8.15 domain of subsystems -/


section Computability

variable (P : ComputablePresentation D)

/-- **The enumeration.** -/
def SubDX (n : ℕ) : Set (List ℕ) := nbhdGen P (decodeList n)

/-- **`SubDX(appendListCode n m) = SubDX n ∩ SubDX m` exactly** (not just when consistent) —
`appendListCode_eq` turns list-code concatenation into `List` `++`, then `nbhdGen_inter`. -/
theorem SubDX_inter_eq (n m : ℕ) :
    SubDX P (appendListCode n m) = SubDX P n ∩ SubDX P m := by
  show nbhdGen P (decodeList (appendListCode n m))
      = nbhdGen P (decodeList n) ∩ nbhdGen P (decodeList m)
  rw [appendListCode_eq, nbhdGen_inter]

theorem SubDX_masterIdx_spec : SubDX P (encodeList ([] : List ℕ)) = (SubD P).master := by
  show nbhdGen P (decodeList (encodeList ([] : List ℕ))) = nbhdGen P []
  rw [decodeList_encodeList]

theorem SubDX_mem (n : ℕ) : (SubD P).mem (SubDX P n) := ⟨decodeList n, rfl⟩

theorem SubDX_surj {N : Set (List ℕ)} (hN : (SubD P).mem N) : ∃ n, SubDX P n = N := by
  obtain ⟨js, rfl⟩ := hN
  exact ⟨encodeList js, by unfold SubDX; rw [decodeList_encodeList]⟩

/-- **Consistency is always true** (`appendListCode n m` is always a witness), hence trivially
recursively decidable. -/
theorem SubD_cons_computable :
    RecDecidable₂ (fun n m => ∃ k, SubDX P k ⊆ SubDX P n ∩ SubDX P m) := by
  refine recDecidable_of_forall (fun t => ⟨appendListCode t.unpair.1 t.unpair.2, ?_⟩)
  rw [SubDX_inter_eq]


/-- The index-component of `consUpd`'s fold state, after processing `el`, is independent of the
flag threaded alongside it: it only accumulates `P.inter` along the entries *selected* by the
bitmask `b`. Pure computation fact, no consistency needed. -/
theorem consUpd_foldl_idx (projFn fc : ℕ → ℕ) (el : List ℕ) (b a flag : ℕ) :
    (List.foldl (fun s x => consUpd P projFn fc s x) (Nat.pair b (Nat.pair a flag)) el).unpair.2.unpair.1
      = (List.map projFn (bitSelect el b)).foldl (fun acc j => P.inter acc j) a := by
  induction el generalizing b a flag with
  | nil => rw [bitSelect_nil, List.foldl_nil, List.map_nil, List.foldl_nil, unpair_pair_snd,
      unpair_pair_fst]
  | cons e el ih =>
    rw [List.foldl_cons, consUpd_eval, bitSelect_cons]
    by_cases hb : b % 2 = 1
    · rw [ite_eq_left hb, List.map_cons, List.foldl_cons, hb, selectFn_one]
      exact ih (b / 2) (P.inter a (projFn e)) _
    · rw [ite_eq_right hb, show b % 2 = 0 by omega, selectFn_zero]
      exact ih (b / 2) a flag


/-- `idxCharAt fc w` (`w = pair b c`): the same fold as `consCharAt`, projecting the running
intersection *index* instead of the consistency flag. -/
def idxCharAt (fc : ℕ → ℕ) (w : ℕ) : ℕ :=
  (foldCode (consStp P id fc) 0 (Nat.pair w.unpair.1 (Nat.pair P.masterIdx 1))
    w.unpair.2).unpair.2.unpair.1

/-- **`idxCharAt` computes `idxchain (bitSelect (decodeList c) b)`.** Unfolds `foldCode` to a
`List.foldl` over `decodeList c`, identifies it with `consUpd`'s fold via `consStp`'s definition,
and reads off the index component via `consUpd_foldl_idx` (at `projFn := id`, `a := masterIdx`,
matching `idxchain`'s own definition as a fold from `masterIdx`). -/
theorem idxCharAt_eq_idxchain (fc : ℕ → ℕ) (w : ℕ) :
    idxCharAt P fc w = idxchain P (bitSelect (decodeList w.unpair.2) w.unpair.1) := by
  unfold idxCharAt idxchain
  rw [foldCode_eq']
  have hstep : (fun acc x => consStp P id fc (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => consUpd P id fc acc x) := by
    funext acc x
    show consStp P id fc (Nat.pair x (Nat.pair acc 0)) = _
    unfold consStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, consUpd_foldl_idx P id fc (decodeList w.unpair.2) w.unpair.1 P.masterIdx 1,
    List.map_id]


theorem primrec_idxCharAt {fc : ℕ → ℕ} (hfcp : Nat.Primrec fc) :
    Nat.Primrec (idxCharAt P fc) := by
  have hfold := primrec_foldCode (primrec_consStp P primrec_id hfcp) (Nat.Primrec.const 0)
    (Nat.Primrec.left.pair ((Nat.Primrec.const P.masterIdx).pair (Nat.Primrec.const 1)))
    Nat.Primrec.right
  exact Nat.Primrec.left.comp (Nat.Primrec.right.comp hfold)

/-- **A generator `P.X m` belongs to `Fin(decodeList c)` iff some bitmask-selected sublist of
`decodeList c` (`b < 2^c`, using `decodeList_length_le`) is `D`-consistent and equals `P.X m`** —
consistency via `consFold_decidable`, equality via `idxCharAt_eq_idxchain` + `idxchain_spec` +
`P.eq_computable`. The `D.mem (P.X m)` conjunct in `finGen`'s definition is always true
(`P.mem_X`), so it drops out of the decidable content. -/
theorem mem_finGen_computable :
    RecDecidable₂ (fun m c => P.X m ∈ finGen P (decodeList c)) := by
  obtain ⟨fc, hfcp, hfcs⟩ := P.cons_computable
  have hfc : ∀ s, fc s = 1 ↔ ∃ k, P.X k ⊆ P.X s.unpair.1 ∩ P.X s.unpair.2 := fun s => (hfcs s).symm
  have hconsFold := consFold_decidable P id fc hfc primrec_id hfcp
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.1 w.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hp1 : RecDecidable (fun w : ℕ =>
      D.mem (interFrom P D.master (bitSelect (decodeList w.unpair.2.unpair.2) w.unpair.1))) := by
    refine RecDecidable.of_iff (fun w => ?_) (hconsFold.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd, List.map_id]
  have hidx : Nat.Primrec (fun w : ℕ => idxCharAt P fc (Nat.pair w.unpair.1 w.unpair.2.unpair.2)) :=
    (primrec_idxCharAt P hfcp).comp hg
  have hh : Nat.Primrec (fun w : ℕ =>
      Nat.pair w.unpair.2.unpair.1 (idxCharAt P fc (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    (Nat.Primrec.left.comp Nat.Primrec.right).pair hidx
  have hp2 : RecDecidable (fun w : ℕ =>
      P.X w.unpair.2.unpair.1 = P.X (idxCharAt P fc (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) := by
    refine RecDecidable.of_iff (fun w => ?_) (P.eq_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hp := hp1.and hp2
  have hbound : Nat.Primrec (fun n : ℕ => 2 ^ n.unpair.2) := primrec_two_pow Nat.Primrec.right
  have hbe := hp.bExists (bound := fun n : ℕ => 2 ^ n.unpair.2) hbound
  refine RecDecidable.of_iff (fun t => ?_) hbe
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨sub, hsub, -, hYeq⟩
    obtain ⟨b, hb, hbeq⟩ := exists_bitSelect_lt hsub
    have hb' : b < 2 ^ t.unpair.2 :=
      lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (decodeList_length_le t.unpair.2))
    have hDsub : D.mem (interFrom P D.master sub) := hYeq ▸ P.mem_X t.unpair.1
    refine ⟨b, hb', hbeq ▸ hDsub, ?_⟩
    rw [idxCharAt_eq_idxchain]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hbeq, idxchain_spec P hDsub, ← hYeq]
  · rintro ⟨b, -, hDb, hXeq⟩
    refine ⟨bitSelect (decodeList t.unpair.2) b, bitSelect_sublist _ _, P.mem_X t.unpair.1, ?_⟩
    rw [hXeq, idxCharAt_eq_idxchain]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [idxchain_spec P hDb]

/-- **`Fin(decodeList c1) ⊆ Fin(decodeList c2)` is recursively decidable** — rewrite via
`finGen_le_iff_forall_mem` (at `D' := finGenSys P (decodeList c2)`, a genuine subsystem of `D` by
`finGenSys_subsystem`) to `∀ i ∈ decodeList c1, P.X i ∈ finGen P (decodeList c2)`, which is exactly
`mem_finGen_computable.bForallList`. -/
theorem finGen_subset_computable :
    RecDecidable₂ (fun c1 c2 => finGen P (decodeList c1) ⊆ finGen P (decodeList c2)) := by
  have hiff : ∀ c1 c2, finGen P (decodeList c1) ⊆ finGen P (decodeList c2) ↔
      ∀ i ∈ decodeList c1, P.X i ∈ finGen P (decodeList c2) :=
    fun c1 c2 => finGen_le_iff_forall_mem P (finGenSys_subsystem P (decodeList c2)) (decodeList c1)
  refine RecDecidable.of_iff (fun t => ?_) (mem_finGen_computable P).bForallList
  exact hiff t.unpair.1 t.unpair.2

/-- **`SubDX n ∩ SubDX m = SubDX k` is recursively decidable.** Chain of exact rewrites reduces
membership-equality of a *pairwise* intersection to a *single* subset-decidable statement at the
`appendListCode`-combined index: `nbhdGen(decodeList n) ∩ nbhdGen(decodeList m) = nbhdGen(decodeList
k)` `↔` (`nbhdGen_inter`) `nbhdGen(decodeList n ++ decodeList m) = nbhdGen(decodeList k)` `↔`
(`appendListCode_eq`) `nbhdGen(decodeList(appendListCode n m)) = nbhdGen(decodeList k)` `↔`
(`nbhdGen_eq_iff`) `finGen(decodeList(appendListCode n m)) = finGen(decodeList k)` `↔`
(`Set.Subset.antisymm_iff`) both inclusions, each an instance of `finGen_subset_computable`
reindexed along the primitive-recursive `appendListCode`. -/
theorem SubD_interEq_computable :
    RecDecidable₃ (fun n m k => SubDX P n ∩ SubDX P m = SubDX P k) := by
  have hiff : ∀ n m k, SubDX P n ∩ SubDX P m = SubDX P k ↔
      finGen P (decodeList (appendListCode n m)) ⊆ finGen P (decodeList k) ∧
        finGen P (decodeList k) ⊆ finGen P (decodeList (appendListCode n m)) := by
    intro n m k
    show nbhdGen P (decodeList n) ∩ nbhdGen P (decodeList m) = nbhdGen P (decodeList k) ↔ _
    rw [nbhdGen_inter, ← appendListCode_eq, nbhdGen_eq_iff, Set.Subset.antisymm_iff]
  have hg1 : Nat.Primrec (fun t : ℕ => appendListCode t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_appendListCode.comp
        (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hreindex1 : Nat.Primrec (fun t : ℕ =>
      Nat.pair (appendListCode t.unpair.1 t.unpair.2.unpair.1) t.unpair.2.unpair.2) :=
    hg1.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hreindex2 : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.2 (appendListCode t.unpair.1 t.unpair.2.unpair.1)) :=
    (Nat.Primrec.right.comp Nat.Primrec.right).pair hg1
  have hforward : RecDecidable (fun t : ℕ =>
      finGen P (decodeList (appendListCode t.unpair.1 t.unpair.2.unpair.1)) ⊆
        finGen P (decodeList t.unpair.2.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((finGen_subset_computable P).comp hreindex1)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbackward : RecDecidable (fun t : ℕ =>
      finGen P (decodeList t.unpair.2.unpair.2) ⊆
        finGen P (decodeList (appendListCode t.unpair.1 t.unpair.2.unpair.1))) := by
    refine RecDecidable.of_iff (fun t => ?_) ((finGen_subset_computable P).comp hreindex2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (hforward.and hbackward)
  exact hiff t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2

/-- **Subgoal 4, capstone.** `SubD P` admits a computable presentation, assembled from 4a–4g. -/
def SubDPresentation : ComputablePresentation (SubD P) where
  X := SubDX P
  mem_X := SubDX_mem P
  surj := SubDX_surj P
  interEq_computable := SubD_interEq_computable P
  cons_computable := SubD_cons_computable P
  inter := appendListCode
  inter_primrec := primrec_appendListCode
  inter_spec := fun {n m} _ => SubDX_inter_eq P n m
  masterIdx := encodeList []
  masterIdx_spec := SubDX_masterIdx_spec P

end Computability


section OrderIso

variable (P : ComputablePresentation D)

/-- **Subgoal 3, capstone.** `SubD.Element ≃o {D' ∣ D' ◁ D}` — fully choice-free. Forward map
`toSubsystem`, inverse `ofSubsystem`; order preservation/reflection reduces via Scott's remark
(`Subsystem.subsystem_iff_subset_of_common`) to `mem_nbhdGen_iff` applied pointwise. -/
def subsystemIso : (SubD P).Element ≃o {D' : NeighborhoodSystem α // D' ◁ D} where
  toFun := toSubsystem P
  invFun x := ofSubsystem P x.1 x.2
  left_inv := ofSubsystem_toSubsystem P
  right_inv x := toSubsystem_ofSubsystem P x.1 x.2
  map_rel_iff' := by
    intro a b
    show toSubsystemSys P a ◁ toSubsystemSys P b ↔ (∀ N, a.mem N → b.mem N)
    rw [Subsystem.subsystem_iff_subset_of_common (toSubsystemSys_subsystem P a)
      (toSubsystemSys_subsystem P b)]
    constructor
    · intro hYsub N hN
      obtain ⟨js, rfl⟩ := a.sub hN
      exact (mem_nbhdGen_iff P b js).mpr
        (fun i hi => hYsub ((mem_nbhdGen_iff P a js).mp hN i hi))
    · rintro hab Y ⟨js, haj, hY⟩
      exact ⟨js, hab (nbhdGen P js) haj, hY⟩

end OrderIso


section ComputableElements

variable (P : ComputablePresentation D)

/-- The singleton-list code `i ↦ encodeList [i]` is primitive recursive. -/
theorem primrec_encodeList_singleton : Nat.Primrec (fun i => encodeList [i]) := by
  have : (fun i => encodeList [i]) = fun i => Nat.pair i 0 + 1 := by
    funext i; show Nat.pair i (encodeList ([] : List ℕ)) + 1 = Nat.pair i 0 + 1
    rw [encodeList]
  rw [this]
  exact Nat.Primrec.succ.comp (Nat.Primrec.pair primrec_id (Nat.Primrec.const 0))

/-- **Subgoal 6a.** `x` is a computable element of `SubD P` iff its "index set relative to `P`" —
the set of `P`-indices `i` with `(toSubsystemSys P x).mem (P.X i)` — is recursively enumerable.
`→`: reindex along `decodeList` (`mem_nbhdGen_iff`) then along the singleton-list code. `←`:
`REPred.forall_mem_decodeList` directly. -/
theorem subsystemU_computable_iff_index_set_re (x : (SubD P).Element) :
    ComputableElement (SubDPresentation P) x ↔
      REPred (fun i => (toSubsystemSys P x).mem (P.X i)) := by
  have hiff : ∀ n, x.mem (SubDX P n) ↔ ∀ i ∈ decodeList n, (toSubsystemSys P x).mem (P.X i) := by
    intro n; unfold SubDX; exact mem_nbhdGen_iff P x (decodeList n)
  constructor
  · intro hx
    have hx' : REPred (fun n => ∀ i ∈ decodeList n, (toSubsystemSys P x).mem (P.X i)) :=
      REPred.of_iff (fun n => (hiff n).symm) hx.out
    refine REPred.of_iff (fun i => ?_) (hx'.comp primrec_encodeList_singleton)
    rw [decodeList_encodeList]
    simp only [List.mem_singleton]
    constructor
    · intro h j hj; rw [hj]; exact h
    · intro h; exact h i rfl
  · intro hx
    constructor
    exact REPred.of_iff hiff hx.forall_mem_decodeList

/-- **Subgoals 6b–6d, combined.** `x` is a computable element of `SubD P` iff the index set of
`D'x := toSubsystemSys P x` (relative to `P`'s own enumeration) is the range of a primitive
recursive function — Scott's "index set r.e." reduced (Exercise 7.14) to an explicit enumerator.
`→` (6b): `Exercise714.repred_exists_primrec_range`, seeded by the witness `P.masterIdx`
(`D'x.mem (P.X P.masterIdx) = D'x.mem D.master`, always true). `←` (6c):
`Exercise714.repred_range_primrec`. -/
theorem subsystemU_element_computable_iff (x : (SubD P).Element) :
    ComputableElement (SubDPresentation P) x ↔
      ∃ r : ℕ → ℕ, Nat.Primrec r ∧
        ∀ i, (toSubsystemSys P x).mem (P.X i) ↔ ∃ n, r n = i := by
  rw [subsystemU_computable_iff_index_set_re P x]
  constructor
  · intro hre
    have ha : (toSubsystemSys P x).mem (P.X P.masterIdx) := by
      rw [P.masterIdx_spec]; exact (toSubsystemSys P x).master_mem
    exact Exercise714.repred_exists_primrec_range hre ha
  · rintro ⟨r, hr, hspec⟩
    exact REPred.of_iff hspec (Exercise714.repred_range_primrec hr)

end ComputableElements


section UniversalSubsystem
section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **Subgoal 6f, main corollary.** If `x` is a computable element of `SubD UComputablePresentation`,
then `D'x := toSubsystemSys UComputablePresentation x` is effectively given — completing, for
`D = 𝒰`, the second half of Exercise 8.15: computable elements of `SubD UComputablePresentation`
correspond to effectively presented domains, presented *relative to* `UComputablePresentation`'s own
enumeration (see the 6g note in `arxiv.md` for why the fully general "arbitrary presentation"
converse — genuine "uniqueness of computable numberings" — is out of scope). -/
theorem subsystemU_effectivelyGiven_of_isComputableElement
    (hx : ComputableElement (SubDPresentation UComputablePresentation) x) :
    (toSubsystemSys UComputablePresentation x).IsEffectivelyGiven := by
  obtain ⟨r, hr, hspec⟩ := (subsystemU_element_computable_iff UComputablePresentation x).mp hx
  exact ⟨Q'xPresentation r x hr hspec⟩

end TreeVal2
end UniversalSubsystem

/-- **Exercise 8.15, first half.** If `D` is effectively given, there is an effectively given
neighbourhood system (`SubD P`, on tokens `List ℕ`) whose elements are order-isomorphic to
`{D' ∣ D' ◁ D}` — a *direct*, choice-free construction (Subgoals 1–4), unlike the classical route
through `Exercise222.reprIso` (`Proposition611.subsystemReprIso`). -/
theorem subsystem_isEffectivelyGiven_of_isEffectivelyGiven (hD : D.IsEffectivelyGiven) :
    ∃ V : NeighborhoodSystem (List ℕ), V.IsEffectivelyGiven ∧
      Nonempty (V.Element ≃o {D' : NeighborhoodSystem α // D' ◁ D}) := by
  obtain ⟨P⟩ := hD
  exact ⟨SubD P, ⟨SubDPresentation P⟩, ⟨subsystemIso P⟩⟩

end DomainTheory.NeighbourhoodSystems
