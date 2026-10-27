module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.TreeVal
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

end Computability


section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`Q2X r`: the term-algebra enumeration of `D'x`'s neighbourhoods.** -/
def Q2X (c : ℕ) : Set ℚ := UX (TreeVal r c)

end TreeVal2

end UniversalSubsystem


section Computability

variable (P : ComputablePresentation D)

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

end Computability

section OrderIso

variable (P : ComputablePresentation D)

/-- **The finite-fold lemma.** If every generator `P.X i` (`i ∈ js`) is individually confirmed by
`x` via some witness list, the witnesses can be concatenated (fold over the finite list `js`,
combining via `x.inter_mem`) into a *single* list `js₀` confirmed by `x` with `Fin(js) ⊆
Fin(js₀)`. -/
theorem exists_common_witness (x : (SubD P).Element) {js : List ℕ}
    (h : ∀ i ∈ js, ∃ js', x.mem (nbhdGen P js') ∧ P.X i ∈ finGen P js') :
    ∃ js0, x.mem (nbhdGen P js0) ∧ finGen P js ⊆ finGen P js0 := by
  induction js with
  | nil => exact ⟨[], SubD_master P ▸ x.master_mem, subset_rfl⟩
  | cons j js' ih =>
    obtain ⟨jsj, hxj, hjmem⟩ := h j List.mem_cons_self
    obtain ⟨js0', hx0', hsub0'⟩ := ih (fun i hi => h i (List.mem_cons_of_mem j hi))
    refine ⟨jsj ++ js0', nbhdGen_inter P jsj js0' ▸ x.inter_mem hxj hx0',
      (finGen_le_iff_forall_mem P (finGenSys_subsystem P (jsj ++ js0')) (j :: js')).mpr
        (List.forall_mem_cons.mpr ⟨?_, ?_⟩)⟩
    · exact finGen_mono P (List.sublist_append_left jsj js0') hjmem
    · exact fun i hi =>
        finGen_mono P (List.sublist_append_right jsj js0') (hsub0' (principal_mem_finGen P hi))

end OrderIso


section Computability

variable (P : ComputablePresentation D)

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

end Computability

section OrderIso

variable (P : ComputablePresentation D)

/-- **`interFrom` splits over list concatenation.** A pure membership-characterization fact
(`mem_interFrom` + `List.forall_mem_append`), independent of consistency. -/
theorem interFrom_append_eq (A : Set α) (l1 l2 : List ℕ) :
    interFrom P A (l1 ++ l2) = interFrom P A l1 ∩ interFrom P A l2 := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, mem_interFrom, List.forall_mem_append]
  tauto

end OrderIso


section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`Q2X r`'s intersection function**: literally the `node` constructor. -/
def Q2inter (c1 c2 : ℕ) : ℕ := nodeCode c1 c2

end TreeVal2

end UniversalSubsystem

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`surj` bridge, part 1: embed a `List ℕ` into a term-algebra code.** Left-fold accumulator
mirroring *exactly* the fold shape of `Theorem75.idxchain`/`Q'X` (`Uinter`-folded from the master),
via `nodeCode`/`leafCode` instead of `Uinter`/`r` directly — so that `TreeVal` evaluates it to the
same `U`-index (`TreeVal_listToTreeAux` below). -/
def listToTreeAux : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | acc, j :: l => listToTreeAux (nodeCode acc (leafCode j)) l

end TreeVal2

end UniversalSubsystem

section OrderIso

variable (P : ComputablePresentation D)

/-- **Forward direction: a subsystem induces a filter of `SubD`.** Given `D' ◁ D`, the filter
`ofSubsystem P D' hD'` consists of the neighbourhoods `nbhd(js)` such that `D'` already contains
every singleton generator `P.X i` for `i ∈ js`. -/
def ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) : (SubD P).Element where
  mem N := ∃ js, N = nbhdGen P js ∧ ∀ i ∈ js, D'.mem (P.X i)
  sub := fun ⟨js, hN, _⟩ => ⟨js, hN⟩
  master_mem := ⟨[], rfl, fun i hi => absurd hi List.not_mem_nil⟩
  inter_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl, h2⟩
    exact ⟨js1 ++ js2, nbhdGen_inter P js1 js2, List.forall_mem_append.mpr ⟨h1, h2⟩⟩
  up_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl⟩ hsub
    have hle : finGen P js2 ⊆ finGen P js1 := hsub (self_mem_nbhdGen P js1)
    exact ⟨js2, rfl, (finGen_le_iff_forall_mem P hD' js2).mp
      (hle.trans ((finGen_le_iff_forall_mem P hD' js1).mpr h1))⟩

/-- **A reusable membership characterization**, generalizing the forward half of
`toSubsystem_ofSubsystem_mem`: for *any* `D' ◁ D`, `ofSubsystem P D' hD'` confirms `nbhd(js)`
exactly when `D'` confirms every generator in `js`. -/
theorem mem_ofSubsystem_nbhdGen {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js : List ℕ) :
    (ofSubsystem P D' hD').mem (nbhdGen P js) ↔ ∀ i ∈ js, D'.mem (P.X i) := by
  constructor
  · rintro ⟨js', hjseq, hall⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    refine (finGen_le_iff_forall_mem P hD' js).mp ?_
    rw [hfin]
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall
  · exact fun hall => ⟨js, rfl, hall⟩

end OrderIso

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

theorem primrec_Q2inter : Nat.Primrec (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) := by
  have heq : (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) = fun t => Nat.pair 1 t := by
    funext t; unfold Q2inter nodeCode; rw [pair_unpair]
  rw [heq]
  exact Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.id

end TreeVal2

end UniversalSubsystem


section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

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

end TreeVal2

end UniversalSubsystem

section Computability

variable (P : ComputablePresentation D)

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

/-- **Backward direction: a filter of `SubD` induces a subsystem.** The neighbourhoods are the
`Fin(js)`-members for lists `js` confirmed by the filter `x`. -/
def toSubsystemSys (x : (SubD P).Element) : NeighborhoodSystem α where
  mem Y := ∃ js, x.mem (nbhdGen P js) ∧ Y ∈ finGen P js
  master := D.master
  master_nonempty := D.master_nonempty
  master_mem := ⟨[], x.master_mem, master_mem_finGen P []⟩
  inter_mem := by
    rintro X Y Z ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ ⟨js3, _, hZ⟩ hZsub
    have hDX := finGen_sub_mem P hX
    have hDY := finGen_sub_mem P hY
    have hDZ := finGen_sub_mem P hZ
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, D.inter_mem hDX hDY hDZ hZsub, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]
  sub_master := fun ⟨_, _, hY⟩ => finGen_sub_master P hY

end OrderIso

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

theorem Q2X_masterIdx_spec :
    Q2X r masterCode = (toSubsystemSys UComputablePresentation x).master := by
  show UX (TreeVal r masterCode) = U.master
  rw [TreeVal_master]
  exact UX_UmasterIdx

end TreeVal2

end UniversalSubsystem

section OrderIso

variable (P : ComputablePresentation D)

/-- **`toSubsystemSys x` is a genuine subsystem of `D`.** Uses the same `interFrom_append_eq`
witness-combination argument as `inter_mem`, without needing the extra `Z`-witness. -/
theorem toSubsystemSys_subsystem (x : (SubD P).Element) : toSubsystemSys P x ◁ D where
  master_eq := rfl
  sub := fun ⟨_, _, hY⟩ => finGen_sub_mem P hY
  inter_closed := by
    rintro X Y ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ hXY
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, hXY, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]

/-- **Round trip 2.** `ofSubsystem P (toSubsystem P x).1 (toSubsystem P x).2 = x`. -/
theorem ofSubsystem_toSubsystem (x : (SubD P).Element) :
    ofSubsystem P (toSubsystemSys P x) (toSubsystemSys_subsystem P x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨js, rfl, hall⟩
    obtain ⟨js0, hx0, hsub0⟩ := exists_common_witness P x hall
    exact x.up_mem hx0 ⟨js, rfl⟩ (nbhdGen_antitone P hsub0)
  · intro hx
    obtain ⟨js, rfl⟩ := x.sub hx
    exact ⟨js, rfl, fun i hi => ⟨js, hx, principal_mem_finGen P hi⟩⟩

/-- **Membership transfer, filter form.** Combines round trip 2 with `mem_ofSubsystem_nbhdGen`:
a filter `x` confirms `nbhd(js)` exactly when the reconstructed subsystem `toSubsystemSys P x`
confirms every generator in `js`. The key bridge for `map_rel_iff'` below. -/
theorem mem_nbhdGen_iff (x : (SubD P).Element) (js : List ℕ) :
    x.mem (nbhdGen P js) ↔ ∀ i ∈ js, (toSubsystemSys P x).mem (P.X i) := by
  conv_lhs => rw [← ofSubsystem_toSubsystem P x]
  exact mem_ofSubsystem_nbhdGen P (toSubsystemSys_subsystem P x) js

end OrderIso

section UniversalSubsystem

/-- **`surj` for `Q'X r`.** Every `D'x`-neighbourhood `Y` is some `Q'X r n`: unwind `Y`'s `finGen`
witness `sub`, use `hspec` + `exists_preimage_of_forall_mem` to find a preimage list `sub0` with
`sub0.map r = sub`, and read off `Y` via the *generic* `Theorem75.idxchain_spec` (applicable because
`sub`'s own consistency — `U.mem (interFrom … sub)` — is exactly `hDY` rewritten along `hYeq`). -/
theorem Q'x_surj (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)
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

end UniversalSubsystem

section OrderIso

variable (P : ComputablePresentation D)

/-- **The backward map, packaged as a subsystem.** -/
def toSubsystem (x : (SubD P).Element) : {D' : NeighborhoodSystem α // D' ◁ D} :=
  ⟨toSubsystemSys P x, toSubsystemSys_subsystem P x⟩

/-- **Round trip, membership form.** `toSubsystemSys (ofSubsystem D')` has exactly the same
neighbourhoods as `D'` itself. `→`: unwind the double existential via `nbhdGen_eq_iff` and the
workhorse lemma. `←`: `P.surj` finds an index `n` with `P.X n = Y`; the singleton list `[n]`
witnesses membership on both sides. -/
theorem toSubsystem_ofSubsystem_mem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) (Y : Set α) :
    (toSubsystemSys P (ofSubsystem P D' hD')).mem Y ↔ D'.mem Y := by
  constructor
  · rintro ⟨js, ⟨js', hjseq, hall⟩, hY⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall (hfin ▸ hY)
  · intro hY
    obtain ⟨n, hn⟩ := P.surj (hD'.sub hY)
    refine ⟨[n], ⟨[n], rfl, fun i hi => ?_⟩, hn ▸ principal_mem_finGen P (List.mem_singleton.mpr rfl)⟩
    rw [List.mem_singleton] at hi
    subst hi
    rw [hn]
    exact hY

/-- **Round trip 1.** `toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩`. -/
theorem toSubsystem_ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) :
    toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩ :=
  Subtype.ext (NeighborhoodSystem.ext (toSubsystem_ofSubsystem_mem P D' hD') hD'.master_eq.symm)

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


section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

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

end TreeVal2

end UniversalSubsystem


section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

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

end TreeVal2

end UniversalSubsystem

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`inter_spec` for `Q2X r`.** The hypothesis is exactly what `Uinter_spec` needs (a `UX`-witness
of consistency, transported through `TreeVal`), so `nodeCode n m` genuinely indexes the intersection
— no fallback case to worry about. -/
theorem Q2inter_spec {n m : ℕ} (h : ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) :
    Q2X r (Q2inter n m) = Q2X r n ∩ Q2X r m := by
  obtain ⟨k, hk⟩ := h
  show UX (TreeVal r (nodeCode n m)) = UX (TreeVal r n) ∩ UX (TreeVal r m)
  rw [TreeVal_node]
  exact Uinter_spec ⟨TreeVal r k, hk⟩

end TreeVal2

end UniversalSubsystem

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

theorem TreeVal_listToTreeAux (acc : ℕ) (l : List ℕ) :
    TreeVal r (listToTreeAux acc l) = l.foldl (fun a j => Uinter a (r j)) (TreeVal r acc) := by
  induction l generalizing acc with
  | nil => simp [listToTreeAux]
  | cons j l ih =>
    simp only [listToTreeAux, List.foldl_cons]
    rw [ih, TreeVal_node, TreeVal_leaf]

end TreeVal2

end UniversalSubsystem

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

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

end TreeVal2

end UniversalSubsystem

section UniversalSubsystem

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

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

end TreeVal2

end UniversalSubsystem

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

/-- **The safe-fold invariant.** Folding `Uinter` from a starting point already in `D'x.mem` along a
list all of whose `UX`-images are also in `D'x.mem` stays in `D'x.mem`: `x`'s own *unconditional*
filter closure (`Element.inter_mem`, via `nbhdGen_inter`) combines the two generators' witnessing
index-lists when `Uinter`'s fold genuinely computes an intersection (dichotomy's right disjunct,
using `interFrom_append_eq`), and `D'x.master_mem` handles the fallback (left disjunct). -/
theorem toSubsystemSys_mem_foldl_Uinter (x : (SubD UComputablePresentation).Element) (acc : ℕ)
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
theorem Q'x_mem_X (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)
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
