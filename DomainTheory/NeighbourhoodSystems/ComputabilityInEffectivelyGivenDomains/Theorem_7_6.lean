module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_15

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem fixMap_isComputable
    (gN incl eq : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    ComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp) P
      (fixMap V) := by
  constructor
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  show REPred₂ (fun c ℓ => (fixMap V).rel (Xenum P P gN c) (P.X ℓ))
  refine ⟨fun w =>
      (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.2 = 1
      ∧ incl (Nat.pair (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.1
          w.unpair.2.unpair.2) = 1,
    ?_, ?_⟩
  ·
    have hcc : Nat.Primrec (fun w => fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1) :=
      ((primrec_fixChainChar P fincl hfinclp).comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)).of_eq (fun w => by
          simp only [unpair_pair_fst, unpair_pair_snd])
    have hA : Nat.Primrec (fun w =>
        (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.2) :=
      Nat.Primrec.right.comp hcc
    have hB : Nat.Primrec (fun w => incl (Nat.pair
        (fixChainChar P fincl w.unpair.2.unpair.1 w.unpair.1).unpair.1 w.unpair.2.unpair.2)) :=
      hinclp.comp ((Nat.Primrec.left.comp hcc).pair (Nat.Primrec.right.comp Nat.Primrec.right))
    exact (RecDecidable.natEq hA (Nat.Primrec.const 1)).and
      (RecDecidable.natEq hB (Nat.Primrec.const 1))
  ·
    intro t
    show (fixMap V).rel (Xenum P P gN t.unpair.1) (P.X t.unpair.2) ↔ _
    rw [fixMap_rel_iff P gN hgN t.unpair.1 t.unpair.2]
    constructor
    · rintro ⟨full, hsteps, hlast⟩
      refine ⟨encodeList full, ?_⟩
      simp only [unpair_pair_fst, unpair_pair_snd]
      have hdec : decodeList (encodeList full) = full := decodeList_encodeList full
      obtain ⟨hfst, hsnd⟩ := fixChainChar_spec P fincl t.unpair.1 (encodeList full)
      rw [hdec] at hfst hsnd
      refine ⟨hsnd.mpr
        ((chainDec_iff_gStepsOK P gN hgN fincl hfincl t.unpair.1 full P.masterIdx).mpr hsteps), ?_⟩
      rw [hfst, hincl, unpair_pair_fst, unpair_pair_snd]
      exact hlast
    · rintro ⟨i, hi⟩
      simp only [unpair_pair_fst, unpair_pair_snd] at hi
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨hfst, hsnd⟩ := fixChainChar_spec P fincl t.unpair.1 i
      refine ⟨decodeList i, ?_, ?_⟩
      · exact (chainDec_iff_gStepsOK P gN hgN fincl hfincl t.unpair.1 (decodeList i)
          P.masterIdx).mp (hsnd.mp hi1)
      · rw [← hfst]
        have hi2' := (hincl (Nat.pair (fixChainChar P fincl t.unpair.1 i).unpair.1
          t.unpair.2)).mp hi2
        rwa [unpair_pair_fst, unpair_pair_snd] at hi2'
end

section
set_option linter.unusedVariables false

theorem theorem_76.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V) (gN incl eq : Nat → Nat)
  (hgN :
    ∀ (c : Nat),
      Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.stepFun α α V V
            (@DomainTheory.NeighbourhoodSystems.funListOf α α V V P P (Domain.Recursive.decodeList c)))))
  (hgNp : Nat.Primrec gN)
  (hincl :
    ∀ (s : Nat),
      Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@LE.le (Set α) (@Set.instLE α)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.snd Nat Nat (Nat.unpair s)))))
  (hinclp : Nat.Primrec incl)
  (heq :
    ∀ (s : Nat),
      Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq (Set α)
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.fst Nat Nat (Nat.unpair s)))
          (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P (@Prod.snd Nat Nat (Nat.unpair s)))))
  (heqp : Nat.Primrec eq),
  @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
    (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
    (@DomainTheory.NeighbourhoodSystems.funPresentation α α V V P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
      heq heqp)
    P (@DomainTheory.NeighbourhoodSystems.fixMap α V) :=
  @DomainTheory.NeighbourhoodSystems.fixMap_isComputable
end

namespace Exercise722
open Set Domain.Recursive

section
def boolNat (b : Bool) : ℕ := if b then 1 else 0
end

section
theorem boolNat_eq_one_iff (b : Bool) : boolNat b = 1 ↔ b := by
  cases b <;> simp [boolNat]
end

section
theorem boolNat_zero_one (b : Bool) : boolNat b = 0 ∨ boolNat b = 1 := by
  cases b <;> simp [boolNat]
end

section
def encodeListBool (σ : List Bool) : ℕ := encodeList (σ.map boolNat)
end

section

def SExpr.encode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (encode a) (encode b))
  | .cap a b => Nat.pair 3 (Nat.pair (encode a) (encode b))
end

end Exercise722
namespace Exercise718
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}

def fiber2 (S : Set (ℕ × (ℕ × α))) (i j : ℕ) : Set α := fiber (fiber S i) j

@[simp] theorem mem_fiber2 {S : Set (ℕ × (ℕ × α))} {i j : ℕ} {a : α} :
    a ∈ fiber2 S i j ↔ (i, (j, a)) ∈ S := Iff.rfl

theorem fiber2_inter (S S' : Set (ℕ × (ℕ × α))) (i j : ℕ) :
    fiber2 (S ∩ S') i j = fiber2 S i j ∩ fiber2 S' i j := rfl

theorem fiber2_master (i j : ℕ) :
    fiber2 ((iterSys (iterSys V)).master) i j = V.master := by
  show fiber (fiber ((iterSys (iterSys V)).master) i) j = V.master
  rw [fiber_iterSys_master, fiber_iterSys_master]

theorem fiber2_mono {S S' : Set (ℕ × (ℕ × α))} (h : S ⊆ S') (i j : ℕ) :
    fiber2 S i j ⊆ fiber2 S' i j := fun _ ha => h ha

theorem mem_fiber2_of_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) (i j : ℕ) :
    V.mem (fiber2 S i j) := (hS.1 i).1 j

end

end Exercise718
namespace Exercise722
open Set Domain.Recursive

section
def natBool (n : ℕ) : Option Bool :=
  match n with | 0 => some false | 1 => some true | _ => none
end

section
def decodeListBool (n : ℕ) : Option (List Bool) :=
  (decodeList n).mapM natBool
end

section

def decodeFuel (fuel : ℕ) (n : ℕ) : Option SExpr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match n.unpair.1 with
    | 0 => if n.unpair.2 = 0 then some .sigma else none
    | 1 => (decodeListBool n.unpair.2).map (.single ·)
    | 2 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none
end

section

def SExpr.decode (n : ℕ) : Option SExpr := decodeFuel (n.unpair.2 + 1) n.unpair.1
end

section

def SsysX (n : ℕ) : Set (List Bool) :=
  match SExpr.decode n with
  | none => SsysX_default
  | some e =>
    if decideNonemptyB e then denote e else SsysX_default
end

section
theorem SsysX_mem (n : ℕ) : InS (SsysX n) := by
  unfold SsysX
  cases hdec : SExpr.decode n with
  | none => simp; exact InS.univ
  | some e =>
    by_cases h : decideNonemptyB e = true
    · simp [h]
      exact InS_denote_of_nonempty ((decideNonemptyB_iff e).1 h)
    · simp [h]
      exact InS.univ
end

section
theorem decodeFuel_pair_cap_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cap a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp
end

section
theorem decodeFuel_pair_cat_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cat a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp
end

section
theorem decodeFuel_succ_cap (fuel c : ℕ) (h : c.unpair.1 = 3) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none := by
  simp [decodeFuel, h]
end

section
theorem decodeFuel_succ_cat (fuel c : ℕ) (h : c.unpair.1 = 2) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none := by
  simp [decodeFuel, h]
end

section
theorem decodeFuel_succ_junk (fuel c : ℕ) (h : 4 ≤ c.unpair.1) :
    decodeFuel (fuel + 1) c = none := by
  match tag : c.unpair.1 with
  | 0 | 1 | 2 | 3 => omega
  | t + 4 => simp [decodeFuel, tag]
end

section
theorem decodeFuel_succ_not_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 ≠ 0) :
    decodeFuel (fuel + 1) c = none := by simp [decodeFuel, h, hσ]
end

section
theorem decodeFuel_succ_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 = 0) :
    decodeFuel (fuel + 1) c = some .sigma := by simp [decodeFuel, h, hσ]
end

section
theorem decodeFuel_succ_single (fuel c : ℕ) (h : c.unpair.1 = 1) :
    decodeFuel (fuel + 1) c = (decodeListBool c.unpair.2).map (.single ·) := by
  simp [decodeFuel, h]
end

section
theorem decodeListBool_encodeListBool (σ : List Bool) :
    decodeListBool (encodeListBool σ) = some σ := by
  simp [decodeListBool, encodeListBool, decodeList_encodeList, List.mapM_map]
  induction σ with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [boolNat, natBool, ih]
end

section
theorem natBinDigit_of_natBool_some (n : ℕ) {b : Bool} (h : natBool n = some b) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool] at h; exact Or.inl rfl
  | 1 => simp [natBool] at h; exact Or.inr rfl
  | n + 2 => simp [natBool] at h
end

section
theorem natBool_isSome_iff (n : ℕ) :
    (natBool n).isSome = true ↔ n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool]
  | 1 => simp [natBool]
  | n + 2 => simp [natBool]
end

section
theorem mapM_natBool_isSome_iff (l : List ℕ) :
    (l.mapM natBool).isSome = true ↔ ∀ x ∈ l, x = 0 ∨ x = 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons]
    constructor
    · intro h
      cases hnx : natBool x with
      | none => simp [hnx] at h
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [hnx, htx] at h
        | some ts =>
          have hxs' : (xs.mapM natBool).isSome = true := by simp [htx]
          intro y hy
          rcases List.mem_cons.mp hy with hEq | hyTail
          · rw [hEq]
            exact natBinDigit_of_natBool_some x hnx
          · exact ih.mp hxs' y hyTail
    · intro h
      have hx : (natBool x).isSome = true :=
        (natBool_isSome_iff x).2 (h x (List.mem_cons_self ..))
      have hxs : (xs.mapM natBool).isSome = true :=
        ih.mpr fun y hy => h y (List.mem_cons_of_mem x hy)
      cases hnx : natBool x with
      | none =>
        rcases h x (List.mem_cons_self ..) with h0 | h1
        · subst h0; simp [natBool] at hnx
        · subst h1; simp [natBool] at hnx
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [htx] at hxs
        | some ts => simp
end

section

theorem decodeListBool_isSome_iff (n : ℕ) :
    (decodeListBool n).isSome = true ↔ allBinDigitsChar n = 1 := by
  simp only [decodeListBool, mapM_natBool_isSome_iff, allBinDigitsChar_eq_one_iff]
end

section

theorem decodeFuelOkChar_eq_one_iff (fuel c : ℕ) :
    decodeFuelOkChar fuel c = 1 ↔ (decodeFuel fuel c).isSome = true := by
  induction fuel generalizing c with
  | zero =>
    simp [decodeFuelOkChar, decodeFuel]
  | succ fuel ih =>
    simp only [decodeFuelOkChar]
    rw [decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      rw [show decodeFuel (fuel + 1) c = if c.unpair.2 = 0 then some .sigma else none from by
        by_cases hσ : c.unpair.2 = 0 <;> simp [decodeFuel, tag, hσ]]
      simp [selectFn_isOne_one_sub_sigma]
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag]
      simp [decodeListBool_isSome_iff, Option.isSome_map]
    | 2 =>
      simp
      rw [decodeFuel_succ_cat fuel c tag, mulBit_eq_one_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      cases hL : decodeFuel fuel c.unpair.2.unpair.1 <;>
        cases hR : decodeFuel fuel c.unpair.2.unpair.2 <;>
        simp [hL, hR, ih1, ih2]
    | 3 =>
      simp
      rw [decodeFuel_succ_cap fuel c tag, mulBit_eq_one_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      cases hL : decodeFuel fuel c.unpair.2.unpair.1 <;>
        cases hR : decodeFuel fuel c.unpair.2.unpair.2 <;>
        simp [hL, hR, ih1, ih2]
    | t + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)]
      simp
end

end Exercise722
namespace Exercise718
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}

def reindexF (W : Set (ℕ × α)) : Set (ℕ × (ℕ × α)) :=
  {p | p.2.2 ∈ fiber W (Nat.pair p.1 p.2.1)}

@[simp] theorem fiber2_reindexF (W : Set (ℕ × α)) (i j : ℕ) :
    fiber2 (reindexF W) i j = fiber W (Nat.pair i j) := rfl

def reindexG (S : Set (ℕ × (ℕ × α))) : Set (ℕ × α) :=
  {p | p.2 ∈ fiber2 S (Nat.unpair p.1).1 (Nat.unpair p.1).2}

@[simp] theorem fiber_reindexG (S : Set (ℕ × (ℕ × α))) (k : ℕ) :
    fiber (reindexG S) k = fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := rfl

theorem exists_inner_bound {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    ∀ n, ∃ M, ∀ i, i < n → ∀ j, M ≤ j → fiber2 S i j = V.master := by
  intro n
  induction n with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨Mn, hMn⟩ := (hS.1 n).2
    refine ⟨max M Mn, fun i hi j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact hM i hlt j (le_trans (le_max_left _ _) hj)
    · subst heq
      exact hMn j (le_trans (le_max_right _ _) hj)

theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have hms : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  have hlt : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
    unfold Nat.pair
    rcases lt_or_ge x y with h | h
    · rw [ite_eq_left h, show max x y = y by omega, hms]; omega
    · rw [ite_eq_right (by omega), show max x y = x by omega, hms]; omega
  have hle : max i j * max i j ≤ Nat.pair i j := by
    unfold Nat.pair
    rcases lt_or_ge i j with h | h
    · rw [ite_eq_left h, show max i j = j by omega]; omega
    · rw [ite_eq_right (by omega), show max i j = i by omega]; omega
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

theorem reindexF_mem {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    (iterSys (iterSys V)).mem (reindexF W) := by
  obtain ⟨hWf, Nw, hNw⟩ := hW
  refine ⟨fun i => ⟨fun j => ?_, Nw, fun j hj => ?_⟩, Nw, fun i hi => ?_⟩
  ·
    show V.mem (fiber2 (reindexF W) i j)
    rw [fiber2_reindexF]; exact hWf (Nat.pair i j)
  ·
    show fiber2 (reindexF W) i j = V.master
    rw [fiber2_reindexF]
    exact hNw (Nat.pair i j) (le_trans hj (le_pair_right i j))
  ·
    apply eq_of_fiber_eq
    intro j
    show fiber2 (reindexF W) i j = fiber ((iterSys V).master) j
    rw [fiber2_reindexF, fiber_iterSys_master]
    exact hNw (Nat.pair i j) (le_trans hi (le_pair_left i j))

theorem reindexF_subset_iff {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    reindexF W ⊆ S ↔ ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := by
  constructor
  · intro h i j
    have := fiber2_mono h i j
    rwa [fiber2_reindexF] at this
  · intro h
    refine subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))
    show fiber2 (reindexF W) i j ⊆ fiber2 S i j
    rw [fiber2_reindexF]; exact h i j

def Fmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (iterSys (iterSys V)) where
  rel W S := (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
    ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, (iterSys (iterSys V)).master_mem, fun i j => by
    rw [fiber_iterSys_master, fiber2_master]⟩
  inter_right := by
    rintro W S S' ⟨hW, hS, hf⟩ ⟨-, hS', hf'⟩
    refine ⟨hW, (iterSys (iterSys V)).inter_mem hS hS' (reindexF_mem hW) ?_, fun i j => ?_⟩
    · exact Set.subset_inter (reindexF_subset_iff.mpr hf) (reindexF_subset_iff.mpr hf')
    · rw [fiber2_inter]; exact Set.subset_inter (hf i j) (hf' i j)
  mono := by
    rintro W W' S S' ⟨hW, hS, hf⟩ hW'W hSS' hW' hS'
    exact ⟨hW', hS', fun i j => ((fiber_mono hW'W _).trans (hf i j)).trans (fiber2_mono hSS' i j)⟩

@[simp] theorem Fmap_rel {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    (Fmap V).rel W S ↔ (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
      ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := Iff.rfl

theorem reindexG_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    (iterSys V).mem (reindexG S) := by
  obtain ⟨No, hNo⟩ := hS.2
  obtain ⟨M, hM⟩ := exists_inner_bound hS No
  refine ⟨fun k => ?_, Nat.pair No M, fun k hk => ?_⟩
  ·
    rw [fiber_reindexG]; exact mem_fiber2_of_mem hS _ _
  ·
    rw [fiber_reindexG]
    set i := (Nat.unpair k).1 with hi
    set j := (Nat.unpair k).2 with hj
    by_cases hiN : i < No
    · by_cases hjM : j < M
      · exfalso
        have hklt : Nat.pair i j < Nat.pair No M := pair_lt_pair_of_lt hiN hjM
        rw [pair_unpair] at hklt
        omega
      · exact hM i hiN j (not_lt.mp hjM)
    · have h1 : fiber S i = (iterSys V).master := hNo i (not_lt.mp hiN)
      show fiber2 S i j = V.master
      rw [fiber2, h1, fiber_iterSys_master]

theorem reindexG_subset_iff {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    reindexG S ⊆ W ↔ ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := by
  constructor
  · intro h k
    have := fiber_mono h k
    rwa [fiber_reindexG] at this
  · intro h
    refine subset_of_fiber_subset (fun k => ?_)
    rw [fiber_reindexG]; exact h k

def Gmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys (iterSys V)) (iterSys V) where
  rel S W := (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
    ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys (iterSys V)).master_mem, (iterSys V).master_mem, fun k => by
    rw [fiber2_master, fiber_iterSys_master]⟩
  inter_right := by
    rintro S W W' ⟨hS, hW, hg⟩ ⟨-, hW', hg'⟩
    refine ⟨hS, (iterSys V).inter_mem hW hW' (reindexG_mem hS) ?_, fun k => ?_⟩
    · exact Set.subset_inter (reindexG_subset_iff.mpr hg) (reindexG_subset_iff.mpr hg')
    · rw [fiber_inter]; exact Set.subset_inter (hg k) (hg' k)
  mono := by
    rintro S S' W W' ⟨hS, hW, hg⟩ hS'S hWW' hS' hW'
    exact ⟨hS', hW', fun k => ((fiber2_mono hS'S _ _).trans (hg k)).trans (fiber_mono hWW' k)⟩

@[simp] theorem Gmap_rel {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    (Gmap V).rel S W ↔ (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
      ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := Iff.rfl

theorem Fmap_comp_Gmap : (Fmap V).comp (Gmap V) = idMap (iterSys (iterSys V)) := by
  apply ApproximableMap.ext
  intro S S'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hS, hW, hg⟩, ⟨-, hS', hf⟩⟩
    refine ⟨hS, hS', subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))⟩
    show fiber2 S i j ⊆ fiber2 S' i j
    have h1 : fiber2 S i j ⊆ fiber W (Nat.pair i j) := by
      have := hg (Nat.pair i j)
      rwa [unpair_pair_fst, unpair_pair_snd] at this
    exact h1.trans (hf i j)
  · rintro ⟨hS, hS', hSS'⟩
    refine ⟨reindexG S, ⟨hS, reindexG_mem hS, ?_⟩, ⟨reindexG_mem hS, hS', ?_⟩⟩
    · intro k; rw [fiber_reindexG]
    · intro i j
      rw [fiber_reindexG, unpair_pair_fst, unpair_pair_snd]
      exact fiber2_mono hSS' i j

theorem Gmap_comp_Fmap : (Gmap V).comp (Fmap V) = idMap (iterSys V) := by
  apply ApproximableMap.ext
  intro W W'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨S, ⟨hW, hS, hf⟩, ⟨-, hW', hg⟩⟩
    refine ⟨hW, hW', subset_of_fiber_subset (fun k => ?_)⟩
    have h1 : fiber W k ⊆ fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := by
      have := hf (Nat.unpair k).1 (Nat.unpair k).2
      rwa [pair_unpair] at this
    exact h1.trans (hg k)
  · rintro ⟨hW, hW', hWW'⟩
    refine ⟨reindexF W, ⟨hW, reindexF_mem hW, ?_⟩, ⟨reindexF_mem hW, hW', ?_⟩⟩
    · intro i j; rw [fiber2_reindexF]
    · intro k
      rw [fiber2_reindexF, pair_unpair]
      exact fiber_mono hWW' k

end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem fiber2_iterEnum_iter (m i j : ℕ) :
    fiber2 (iterEnum (iterPresentation P) m) i j
      = P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  show fiber (fiber (iterEnum (iterPresentation P) m) i) j = _
  rw [fiber_iterEnum, iterPresentation_X, fiber_iterEnum]
end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)
variable {P}

theorem Gmap_rel_enum_iff (s n : ℕ) :
    (Gmap V).rel (iterEnum (iterPresentation P) s) (iterEnum P n) ↔
      ∀ k, k < n →
        P.X (iterIdx P (iterIdx (iterPresentation P) s (Nat.unpair k).1) (Nat.unpair k).2)
          ⊆ P.X (iterIdx P n k) := by
  rw [Gmap_rel]
  have hmem₁ := iterEnum_mem (P := iterPresentation P) s
  have hmem₂ := iterEnum_mem (P := P) n
  constructor
  · rintro ⟨-, -, hg⟩ k _
    have := hg k
    rwa [fiber2_iterEnum_iter, fiber_iterEnum] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun k => ?_⟩
    rw [fiber2_iterEnum_iter, fiber_iterEnum]
    by_cases hk : k < n
    · exact hbd k hk
    · rw [iterIdx_ge (not_lt.mp hk), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

theorem Gmap_isComputable :
    ComputableMap (iterPresentation (iterPresentation P)) (iterPresentation P) (Gmap V) := by
  constructor

  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair
          ((Nat.Primrec.left.comp Nat.Primrec.left).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2 u.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) ⊆ P.X (iterIdx P u.unpair.2.unpair.2 u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₀ := hp₂.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re
  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Gmap_rel_enum_iff t.unpair.1 t.unpair.2

end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem masterIdx_iterPresentation : (iterPresentation P).masterIdx = 0 := rfl
end

section
variable {α β : Type*}
variable {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)
variable {P}

theorem Fmap_rel_enum_iff (n m : ℕ) :
    (Fmap V).rel (iterEnum P n) (iterEnum (iterPresentation P) m) ↔
      ∀ i, i < m → ∀ j, j < iterIdx (iterPresentation P) m i →
        P.X (iterIdx P n (Nat.pair i j)) ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  rw [Fmap_rel]
  have hmem₁ := iterEnum_mem (P := P) n
  have hmem₂ := iterEnum_mem (P := iterPresentation P) m
  constructor
  · rintro ⟨-, -, hf⟩ i _ j _
    have := hf i j
    rwa [fiber_iterEnum, fiber2_iterEnum_iter] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun i j => ?_⟩
    rw [fiber_iterEnum, fiber2_iterEnum_iter]
    by_cases hi : i < m
    · by_cases hj : j < iterIdx (iterPresentation P) m i
      · exact hbd i hi j hj
      ·
        rw [iterIdx_ge (not_lt.mp hj), P.masterIdx_spec]
        exact V.sub_master (P.mem_X _)
    ·
      have h0 : iterIdx (iterPresentation P) m i = 0 := by
        rw [iterIdx_ge (not_lt.mp hi), masterIdx_iterPresentation]
      rw [h0, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

theorem Fmap_isComputable :
    ComputableMap (iterPresentation P) (iterPresentation (iterPresentation P)) (Fmap V) := by
  constructor

  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1)) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left).pair
          (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1)
        u.unpair.1) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1))
        ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2
          u.unpair.2.unpair.1) u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]

  have hbound₂ : Nat.Primrec (fun v : ℕ =>
      iterIdx (iterPresentation P) v.unpair.2.unpair.2 v.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq
      (fun v => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₁ := hp₂.bForall hbound₂
  have hp₀ := hp₁.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re

  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Fmap_rel_enum_iff t.unpair.1 t.unpair.2

def iterIterEffectiveIso (P : ComputablePresentation V) :
    EffectiveIso (iterPresentation P) (iterPresentation (iterPresentation P)) where
  toMap := Fmap V
  invMap := Gmap V
  toMap_computable := Fmap_isComputable
  invMap_computable := Gmap_isComputable
  left_inv := Gmap_comp_Fmap
  right_inv := Fmap_comp_Gmap

end

end Exercise718
namespace Exercise722
open Set Domain.Recursive

section

def safeDecodeActive (n : ℕ) : SExpr :=
  match SExpr.decode n with
  | none => .sigma
  | some e => if decideNonemptyB e then e else .sigma
end

section
theorem SsysX_eq_denote_safe (n : ℕ) : SsysX n = denote (safeDecodeActive n) := by
  unfold SsysX safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => simp [denote_sigma, SsysX_default]
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hb]
    · simp [hb, denote_sigma, SsysX_default]
end

section
theorem safeDecodeActive_nonempty (n : ℕ) : (denote (safeDecodeActive n)).Nonempty := by
  unfold safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => exact Set.univ_nonempty
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hb]; exact (decideNonemptyB_iff e).mp hb
    · simp [hb, denote_sigma]
end

section
theorem consistentB_safe_sigma (n : ℕ) : consistentB (safeDecodeActive n) .sigma = true := by
  rw [consistentB_iff, denote_cap, denote_sigma, Set.inter_univ]
  exact safeDecodeActive_nonempty n
end

section
theorem consistentB_sigma_safe (m : ℕ) : consistentB .sigma (safeDecodeActive m) = true := by
  rw [consistentB_iff, denote_cap, denote_sigma, Set.univ_inter]
  exact safeDecodeActive_nonempty m
end

section

def sexprDepth : SExpr → ℕ
  | .sigma => 1
  | .single _ => 1
  | .cat a b => 1 + max (sexprDepth a) (sexprDepth b)
  | .cap a b => 1 + max (sexprDepth a) (sexprDepth b)
end

section
theorem decodeFuel_encode {fuel : ℕ} {e : SExpr} (h : sexprDepth e ≤ fuel) :
    decodeFuel fuel (SExpr.encode e) = some e := by
  induction e generalizing fuel with
  | sigma =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      simp [decodeFuel, SExpr.encode]
  | single σ =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      simp [decodeFuel, SExpr.encode, decodeListBool_encodeListBool σ]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      have ha : sexprDepth a ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      have hb : sexprDepth b ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      simp [decodeFuel, SExpr.encode, iha ha, ihb hb]
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      have ha : sexprDepth a ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      have hb : sexprDepth b ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      simp [decodeFuel, SExpr.encode, iha ha, ihb hb]
end

section

def SExpr.index (e : SExpr) : ℕ := Nat.pair (encode e) (sexprDepth e)
end

section
theorem SExpr.decode_index (e : SExpr) : decode (index e) = some e := by
  simp [decode, index]
  exact decodeFuel_encode (Nat.le_succ (sexprDepth e))
end

section
theorem SsysX_surj {Y : Set (List Bool)} (hY : InS Y) : ∃ n, SsysX n = Y := by
  obtain ⟨e, he, hne⟩ := inS_iff_exists_denote.mp hY
  refine ⟨SExpr.index e, ?_⟩
  unfold SsysX
  rw [SExpr.decode_index e]
  have hne' : (denote e).Nonempty := he ▸ hne
  have hb : decideNonemptyB e = true := (decideNonemptyB_iff e).2 hne'
  simp [hb, he]
end

section

def ssysActive (n : ℕ) : Bool :=
  match SExpr.decode n with
  | none => false
  | some e => decideNonemptyB e
end

section
theorem safeDecodeActive_inactive (n : ℕ) (h : ssysActive n = false) : safeDecodeActive n = .sigma := by
  dsimp only [ssysActive, safeDecodeActive] at h ⊢
  cases hdec : SExpr.decode n with
  | none => rfl
  | some e =>
    by_cases hb : decideNonemptyB e
    · exfalso
      simp [hdec, hb] at h
    · simp [hb]
end

section

def ssysConsistentB (n m : ℕ) : Bool :=
  if !ssysActive n || !ssysActive m then true
  else
    match SExpr.decode n, SExpr.decode m with
    | some a, some b => consistentB a b
    | _, _ => true
end

section
theorem ssysConsistentB_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  by_cases hn : ssysActive n
  · by_cases hm : ssysActive m
    · cases hdecn : SExpr.decode n with
      | none => exfalso; simp [ssysActive, hdecn] at hn
      | some a =>
        cases hdecm : SExpr.decode m with
        | none => exfalso; simp [ssysActive, hdecm] at hm
        | some b =>
          have ha : decideNonemptyB a := by simpa [ssysActive, hdecn] using hn
          have hb : decideNonemptyB b := by simpa [ssysActive, hdecm] using hm
          have hsa : safeDecodeActive n = a := by simp [safeDecodeActive, hdecn, ha]
          have hsb : safeDecodeActive m = b := by simp [safeDecodeActive, hdecm, hb]
          constructor
          · intro h
            rw [hsa, hsb]
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
            rw [heq] at h
            exact h
          · intro hcons
            rw [hsa, hsb] at hcons
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
            rw [heq]
            exact hcons
    · have hm' : ssysActive m = false := by simpa using hm
      constructor
      · intro _; rw [safeDecodeActive_inactive m hm', consistentB_safe_sigma n]
      · intro _; unfold ssysConsistentB; simp [hn, hm']
  · have hn' : ssysActive n = false := by simpa using hn
    constructor
    · intro _; rw [safeDecodeActive_inactive n hn', consistentB_sigma_safe m]
    · intro _; unfold ssysConsistentB; simp [hn']
end

section
theorem ssys_cons_positivity (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ (SsysX n ∩ SsysX m).Nonempty := by
  constructor
  · intro ⟨k, hk⟩
    exact Set.Nonempty.mono hk (InS.nonempty (SsysX_mem k))
  · intro hne
    have hIn : InS (SsysX n ∩ SsysX m) :=
      (Ssys_isPositive (Ssys_mem.mpr (SsysX_mem n)) (Ssys_mem.mpr (SsysX_mem m))).2 hne
    obtain ⟨k, hk⟩ := SsysX_surj hIn
    exact ⟨k, hk.subset⟩
end

section
theorem ssys_inter_nonempty_iff_consistent (n m : ℕ) :
    (SsysX n ∩ SsysX m).Nonempty ↔ consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, ← denote_cap, consistentB_iff]
end

section
theorem ssys_cons_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [ssys_cons_positivity, ssys_inter_nonempty_iff_consistent]
end

section
theorem ssys_cons_char_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔ ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m := by
  rw [ssysConsistentB_iff, ssys_cons_iff]
end

section

instance decidableSsysCons (n m : ℕ) :
    Decidable (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  decidable_of_iff (ssysConsistentB n m = true) (ssys_cons_char_iff n m)
end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_presentation_inst47 : ∀ (n m : Nat),
  Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.Exercise722.ssysConsistentB n m) Bool.true)
    (∃ (k : Nat),
      @LE.le (Set (List Bool)) (@Set.instLE (List Bool)) (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX k)
        (@Inter.inter (Set (List Bool)) (@Set.instInter (List Bool))
          (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX n)
          (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX m))) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.ssys_cons_char_iff
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise722
open Set Domain.Recursive

section
set_option maxHeartbeats 5000000

class PartiallyEffectivelyGiven (V : NeighborhoodSystem α) : Prop where
  out : Nonempty (ConsistencyPresentation V)

theorem c9b5_encodeListBool_eq (σ : List Bool) :
    Domain.Recursive.c9b5_encodeListBool σ = encodeListBool σ := by
  unfold Domain.Recursive.c9b5_encodeListBool encodeListBool
  congr 1

theorem c9b5_sexprDepth_eq (e : SExpr) : Domain.Recursive.c9b5_sexprDepth e = sexprDepth e := by
  induction e with
  | sigma => rfl
  | single _ => rfl
  | cat a b iha ihb => simp [Domain.Recursive.c9b5_sexprDepth, sexprDepth, iha, ihb]
  | cap a b iha ihb => simp [Domain.Recursive.c9b5_sexprDepth, sexprDepth, iha, ihb]

theorem c9b5_sexprGodelEncode_eq (e : SExpr) :
    Domain.Recursive.c9b5_sexprGodelEncode e = SExpr.encode e := by
  induction e with
  | sigma => rfl
  | single σ => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, c9b5_encodeListBool_eq]
  | cat a b iha ihb => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, iha, ihb]
  | cap a b iha ihb => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, iha, ihb]

theorem decodeFuel_depth_le {fuel c : ℕ} {e : SExpr} (h : decodeFuel fuel c = some e) :
    sexprDepth e ≤ fuel := by
  induction fuel generalizing c e with
  | zero => simp [decodeFuel] at h
  | succ fuel ih =>
    match tag : c.unpair.1 with
    | 0 =>
      by_cases hσ : c.unpair.2 = 0
      · rw [decodeFuel_succ_sigma fuel c tag hσ] at h
        simp only [Option.some.injEq] at h
        simp [← h, sexprDepth]
      · rw [decodeFuel_succ_not_sigma fuel c tag hσ] at h; simp at h
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag] at h
      cases hb : decodeListBool c.unpair.2 with
      | none => simp [hb] at h
      | some σ =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp [← h, sexprDepth]
    | 2 =>
      rw [decodeFuel_succ_cat fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hda := ih ha
          have hdb := ih hb
          simp only [← h, sexprDepth]
          omega
    | 3 =>
      rw [decodeFuel_succ_cap fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hda := ih ha
          have hdb := ih hb
          simp only [← h, sexprDepth]
          omega
    | _ + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)] at h; simp at h

theorem natBool_eq_some_iff (n : ℕ) (b : Bool) : natBool n = some b ↔ n = boolNat b := by
  match n with
  | 0 => cases b <;> simp [natBool, boolNat]
  | 1 => cases b <;> simp [natBool, boolNat]
  | n + 2 => cases b <;> simp [natBool, boolNat]

theorem mapM_natBool_eq_some (l : List ℕ) (σ : List Bool)
    (h : l.mapM natBool = some σ) : l = σ.map boolNat := by
  induction l generalizing σ with
  | nil => rw [List.mapM_nil] at h; simpa using h.symm
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hnx : natBool x with
    | none => simp [hnx] at h
    | some b =>
      cases htx : xs.mapM natBool with
      | none => simp [hnx, htx] at h
      | some ys =>
        simp only [hnx, htx] at h
        obtain rfl : σ = b :: ys := by simpa using h.symm
        simp [ih ys htx, (natBool_eq_some_iff x b).mp hnx]

theorem decodeListBool_eq_some (n : ℕ) (σ : List Bool) (h : decodeListBool n = some σ) :
    n = encodeListBool σ := by
  have hl : decodeList n = σ.map boolNat := mapM_natBool_eq_some (decodeList n) σ h
  calc n = encodeList (decodeList n) := (encodeList_decodeList n).symm
    _ = encodeList (σ.map boolNat) := by rw [hl]
    _ = encodeListBool σ := rfl

theorem decodeFuel_sound {fuel c : ℕ} {e : SExpr} (h : decodeFuel fuel c = some e) :
    c = SExpr.encode e := by
  induction fuel generalizing c e with
  | zero => simp [decodeFuel] at h
  | succ fuel ih =>
    match tag : c.unpair.1 with
    | 0 =>
      by_cases hσ : c.unpair.2 = 0
      · have hc : c = Nat.pair 0 0 := by
          have hpu := Nat.pair_unpair c; rw [tag, hσ] at hpu; exact hpu.symm
        rw [decodeFuel_succ_sigma fuel c tag hσ] at h
        simp only [Option.some.injEq] at h
        simp [SExpr.encode, ← h, hc]
      · rw [decodeFuel_succ_not_sigma fuel c tag hσ] at h; simp at h
    | 1 =>
      have hc1 : c = Nat.pair 1 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_single fuel c tag] at h
      cases hb : decodeListBool c.unpair.2 with
      | none => simp [hb] at h
      | some σ =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hσc : c.unpair.2 = encodeListBool σ := decodeListBool_eq_some c.unpair.2 σ hb
        rw [← h, SExpr.encode, hc1, hσc]
    | 2 =>
      have hc2 : c = Nat.pair 2 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_cat fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hac : c.unpair.2.unpair.1 = SExpr.encode a := ih ha
          have hbc : c.unpair.2.unpair.2 = SExpr.encode b := ih hb
          have hpc : c.unpair.2 = Nat.pair (SExpr.encode a) (SExpr.encode b) := by
            have hpu := Nat.pair_unpair c.unpair.2; rw [hac, hbc] at hpu; exact hpu.symm
          rw [← h, SExpr.encode, hc2, hpc]
    | 3 =>
      have hc3 : c = Nat.pair 3 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_cap fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hac : c.unpair.2.unpair.1 = SExpr.encode a := ih ha
          have hbc : c.unpair.2.unpair.2 = SExpr.encode b := ih hb
          have hpc : c.unpair.2 = Nat.pair (SExpr.encode a) (SExpr.encode b) := by
            have hpu := Nat.pair_unpair c.unpair.2; rw [hac, hbc] at hpu; exact hpu.symm
          rw [← h, SExpr.encode, hc3, hpc]
    | _ + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)] at h; simp at h

def ssysActiveChar (n : ℕ) : ℕ :=
  mulBit (decodeFuelOkChar (n.unpair.2 + 1) n.unpair.1)
    (decideNonemptyBChar (n.unpair.2 + 1) n.unpair.1)

theorem primrec_ssysActiveChar : Nat.Primrec ssysActiveChar := by
  have hpack : Nat.Primrec (fun n : ℕ => Nat.pair (n.unpair.2 + 1) n.unpair.1) :=
    Nat.Primrec.pair (primrec_add₂ Nat.Primrec.right (Nat.Primrec.const 1)) Nat.Primrec.left
  have h1 : Nat.Primrec (fun n => decodeFuelOkChar (n.unpair.2 + 1) n.unpair.1) :=
    (primrec_decodeFuelOkChar2.comp hpack).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2 : Nat.Primrec (fun n => decideNonemptyBChar (n.unpair.2 + 1) n.unpair.1) :=
    (primrec_decideNonemptyBChar2.comp hpack).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mulBit.comp (Nat.Primrec.pair h1 h2)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd, ssysActiveChar]

theorem ssysActiveChar_eq_one_iff (n : ℕ) : ssysActiveChar n = 1 ↔ ssysActive n = true := by
  simp only [ssysActiveChar, ssysActive, SExpr.decode, mulBit_eq_one_iff,
    decodeFuelOkChar_eq_one_iff]
  cases hdec : decodeFuel (n.unpair.2 + 1) n.unpair.1 with
  | none => simp
  | some e =>
    have hc : n.unpair.1 = SExpr.encode e := decodeFuel_sound hdec
    have hdepth : Domain.Recursive.c9b5_sexprDepth e ≤ n.unpair.2 + 1 := by
      rw [c9b5_sexprDepth_eq]; exact decodeFuel_depth_le hdec
    simp only [Option.isSome_some, true_and]
    rw [hc, ← c9b5_sexprGodelEncode_eq, decideNonemptyBChar_eq_one_iff hdepth, decideNonemptyB_iff]

theorem ssysActiveChar_le_one (n : ℕ) : ssysActiveChar n ≤ 1 :=
  mulBit_le_one (decodeFuelOkChar_le_one _ _) (bExistsFn_le_one _ _ _)

theorem ssysActive_exists_decode {n : ℕ} (hn : ssysActive n = true) :
    ∃ e, SExpr.decode n = some e := by
  unfold ssysActive at hn
  cases hdec : SExpr.decode n with
  | none => simp [hdec] at hn
  | some e => exact ⟨e, rfl⟩

@[irreducible] def ssysCanonicalCode (n : ℕ) : ℕ :=
  Domain.Recursive.selectFn (ssysActiveChar n) n.unpair.1 (SExpr.encode .sigma)

def ssysConsChar (t : ℕ) : ℕ := boolNat (ssysConsistentB t.unpair.1 t.unpair.2)

theorem ssysConsChar_eq_one_iff (t : ℕ) :
    ssysConsChar t = 1 ↔ ssysConsistentB t.unpair.1 t.unpair.2 = true := by
  simp [ssysConsChar, boolNat_eq_one_iff]

theorem ssysConsChar_le_one (t : ℕ) : ssysConsChar t ≤ 1 := by
  have := boolNat_zero_one (ssysConsistentB t.unpair.1 t.unpair.2)
  unfold ssysConsChar
  omega

theorem ssysConsChar_zero_one (t : ℕ) : ssysConsChar t = 0 ∨ ssysConsChar t = 1 :=
  boolNat_zero_one _

def ssysConsistentBChar (n m : ℕ) : ℕ :=
  selectFn (mulBit (ssysActiveChar n) (ssysActiveChar m))
    (consistentBChar (n.unpair.2 + m.unpair.2 + 2) n.unpair.1 m.unpair.1)
    1

theorem primrec_ssysConsistentBChar :
    Nat.Primrec (fun t => ssysConsistentBChar t.unpair.1 t.unpair.2) := by
  have hcond : Nat.Primrec
      (fun t => mulBit (ssysActiveChar t.unpair.1) (ssysActiveChar t.unpair.2)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair (primrec_ssysActiveChar.comp Nat.Primrec.left)
      (primrec_ssysActiveChar.comp Nat.Primrec.right))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hfuel : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2) :=
    primrec_add₂ (primrec_add₂ (Nat.Primrec.right.comp Nat.Primrec.left)
      (Nat.Primrec.right.comp Nat.Primrec.right)) (Nat.Primrec.const 2)
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2)
      (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1)) :=
    Nat.Primrec.pair hfuel (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
      (Nat.Primrec.left.comp Nat.Primrec.right))
  have hcons : Nat.Primrec (fun t => consistentBChar
      (t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2) t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_consistentBChar2.comp hpack).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hcons (Nat.Primrec.const 1)).of_eq fun t => by
    simp only [ssysConsistentBChar]

theorem ssysConsistentBChar_eq_one_iff (n m : ℕ) :
    ssysConsistentBChar n m = 1 ↔ ssysConsistentB n m = true := by
  unfold ssysConsistentBChar ssysConsistentB
  by_cases hn : ssysActive n = true
  · by_cases hm : ssysActive m = true
    · have hnc : ssysActiveChar n = 1 := (ssysActiveChar_eq_one_iff n).mpr hn
      have hmc : ssysActiveChar m = 1 := (ssysActiveChar_eq_one_iff m).mpr hm
      obtain ⟨a, hdecn⟩ := ssysActive_exists_decode hn
      obtain ⟨b, hdecm⟩ := ssysActive_exists_decode hm
      have hac : n.unpair.1 = SExpr.encode a := decodeFuel_sound hdecn
      have hbc : m.unpair.1 = SExpr.encode b := decodeFuel_sound hdecm
      have hda : sexprDepth a ≤ n.unpair.2 + 1 := decodeFuel_depth_le hdecn
      have hdb : sexprDepth b ≤ m.unpair.2 + 1 := decodeFuel_depth_le hdecm
      have hfuel : Domain.Recursive.c9b5_sexprDepth (.cap a b) ≤ n.unpair.2 + m.unpair.2 + 2 := by
        rw [c9b5_sexprDepth_eq]
        simp only [sexprDepth]
        omega
      simp only [hnc, hmc, mulBit, mul_one, selectFn_one]
      rw [hac, hbc, ← c9b5_sexprGodelEncode_eq, ← c9b5_sexprGodelEncode_eq,
        consistentBChar_eq_one_iff hfuel]
      have hnotinactive : (!ssysActive n || !ssysActive m) = false := by simp [hn, hm]
      rw [hnotinactive, ite_eq_right (by decide)]
      simp only [hdecn, hdecm]
      exact (consistentB_iff a b).symm
    · have hm0 : ssysActiveChar m = 0 := by
        have hle := ssysActiveChar_le_one m
        have hne : ssysActiveChar m ≠ 1 := fun h => hm ((ssysActiveChar_eq_one_iff m).mp h)
        omega
      have hmf : ssysActive m = false := by
        cases hAm : ssysActive m with
        | false => rfl
        | true => exact absurd hAm hm
      simp only [hm0, mulBit, mul_zero, selectFn_zero, hmf, Bool.not_false, Bool.or_true, ite_true]
  · have hn0 : ssysActiveChar n = 0 := by
      have hle := ssysActiveChar_le_one n
      have hne : ssysActiveChar n ≠ 1 := fun h => hn ((ssysActiveChar_eq_one_iff n).mp h)
      omega
    have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    simp only [hn0, mulBit, zero_mul, selectFn_zero, hnf, Bool.not_false, Bool.true_or, ite_true]

theorem ssysConsistentBChar_le_one (n m : ℕ) : ssysConsistentBChar n m ≤ 1 := by
  unfold ssysConsistentBChar
  rcases (show mulBit (ssysActiveChar n) (ssysActiveChar m) = 0 ∨
      mulBit (ssysActiveChar n) (ssysActiveChar m) = 1 by
    have h1 := ssysActiveChar_le_one n
    have h2 := ssysActiveChar_le_one m
    unfold mulBit
    rcases (show ssysActiveChar n = 0 ∨ ssysActiveChar n = 1 by omega) with hn | hn <;>
      rcases (show ssysActiveChar m = 0 ∨ ssysActiveChar m = 1 by omega) with hm | hm <;>
      simp [hn, hm]) with h0 | h1
  · rw [h0, selectFn_zero]
  · rw [h1, selectFn_one]; exact consistentBChar_le_one _ _ _

theorem ssysConsChar_eq_ssysConsistentBChar (t : ℕ) :
    ssysConsChar t = ssysConsistentBChar t.unpair.1 t.unpair.2 := by
  apply eq_of_le_one_iff_one (ssysConsChar_le_one t) (ssysConsistentBChar_le_one _ _)
  rw [ssysConsChar_eq_one_iff, ssysConsistentBChar_eq_one_iff]

theorem primrec_ssysConsChar : Nat.Primrec ssysConsChar :=
  (primrec_ssysConsistentBChar).of_eq fun t => (ssysConsChar_eq_ssysConsistentBChar t).symm

def ssysInterEqChar (t : ℕ) : ℕ :=
  let n := t.unpair.1
  let m := t.unpair.2.unpair.1
  let k := t.unpair.2.unpair.2
  Domain.Recursive.interEqChar (n.unpair.2 + m.unpair.2 + k.unpair.2 + 3)
    (Domain.Recursive.capCode (ssysCanonicalCode n) (ssysCanonicalCode m)) (ssysCanonicalCode k)

theorem ssys_cons_char_eq_one_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ ssysConsChar (Nat.pair n m) = 1 := by
  rw [ssysConsChar_eq_one_iff, ssys_cons_char_iff, unpair_pair_fst, unpair_pair_snd]

theorem Ssys_cons_computable_of_primrec_ssysConsChar (hf : Nat.Primrec ssysConsChar) :
    RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  RecDecidable₂.of_paired_zero_one_char hf ssysConsChar_zero_one ssys_cons_char_eq_one_iff

theorem Ssys_cons_computable : RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  Ssys_cons_computable_of_primrec_ssysConsChar primrec_ssysConsChar

def SsysPres : ConsistencyPresentation Ssys where
  X := SsysX
  mem_X n := Ssys_mem.mpr (SsysX_mem n)
  surj hY := SsysX_surj (Ssys_mem.mp hY)
  cons_computable := Ssys_cons_computable

theorem c9b5_boolNat_eq (b : Bool) : Domain.Recursive.c9b5_boolNat b = boolNat b := by
  cases b <;> rfl

theorem ssysCanonicalCode_eq (n : ℕ) : ssysCanonicalCode n = SExpr.encode (safeDecodeActive n) := by
  unfold ssysCanonicalCode
  by_cases hn : ssysActive n = true
  · rw [(ssysActiveChar_eq_one_iff n).mpr hn, Domain.Recursive.selectFn_one]
    obtain ⟨e, hdec⟩ := ssysActive_exists_decode hn
    have hac : n.unpair.1 = SExpr.encode e := decodeFuel_sound hdec
    rw [hac]
    congr 1
    unfold safeDecodeActive
    rw [hdec]
    have : decideNonemptyB e = true := by
      unfold ssysActive at hn; rw [hdec] at hn; exact hn
    simp [this]
  · have hn0 : ssysActiveChar n = 0 := by
      have hle := ssysActiveChar_le_one n
      have hne : ssysActiveChar n ≠ 1 := fun h => hn ((ssysActiveChar_eq_one_iff n).mp h)
      omega
    have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    rw [hn0, Domain.Recursive.selectFn_zero, safeDecodeActive_inactive n hnf]

theorem sexprDepth_safeDecodeActive_le (n : ℕ) : sexprDepth (safeDecodeActive n) ≤ n.unpair.2 + 1 := by
  by_cases hn : ssysActive n = true
  · obtain ⟨e, hdec⟩ := ssysActive_exists_decode hn
    have hda : sexprDepth e ≤ n.unpair.2 + 1 := decodeFuel_depth_le hdec
    have heq : safeDecodeActive n = e := by
      unfold safeDecodeActive
      rw [hdec]
      have : decideNonemptyB e = true := by
        unfold ssysActive at hn; rw [hdec] at hn; exact hn
      simp [this]
    rw [heq]; exact hda
  · have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    rw [safeDecodeActive_inactive n hnf]
    simp [sexprDepth]

theorem ssys_interEq_iff (n m k : ℕ) :
    SsysX n ∩ SsysX m = SsysX k ↔
      denote (.cap (safeDecodeActive n) (safeDecodeActive m)) = denote (safeDecodeActive k) := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, SsysX_eq_denote_safe, denote_cap]

theorem ssysInterEqChar_le_one (t : ℕ) : ssysInterEqChar t ≤ 1 := by
  unfold ssysInterEqChar
  exact Domain.Recursive.interEqChar_le_one _ _ _

theorem ssysInterEqChar_eq_one_iff (n m k : ℕ) :
    ssysInterEqChar (Nat.pair n (Nat.pair m k)) = 1 ↔ SsysX n ∩ SsysX m = SsysX k := by
  unfold ssysInterEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [ssys_interEq_iff]
  have hfuel : n.unpair.2 + m.unpair.2 + k.unpair.2 + 3 ≥
      c9b5_sexprDepth (.cap (safeDecodeActive n) (safeDecodeActive m)) ∧
      n.unpair.2 + m.unpair.2 + k.unpair.2 + 3 ≥ c9b5_sexprDepth (safeDecodeActive k) := by
    rw [c9b5_sexprDepth_eq, c9b5_sexprDepth_eq]
    have hn := sexprDepth_safeDecodeActive_le n
    have hm := sexprDepth_safeDecodeActive_le m
    have hk := sexprDepth_safeDecodeActive_le k
    simp only [sexprDepth]
    omega
  rw [show Domain.Recursive.capCode (ssysCanonicalCode n) (ssysCanonicalCode m) =
      c9b5_sexprGodelEncode (.cap (safeDecodeActive n) (safeDecodeActive m)) from ?_,
    show ssysCanonicalCode k = c9b5_sexprGodelEncode (safeDecodeActive k) from ?_,
    Domain.Recursive.interEqChar_eq_one_iff hfuel.1 hfuel.2]
  · rw [c9b5_sexprGodelEncode_eq]; exact ssysCanonicalCode_eq k
  · unfold Domain.Recursive.capCode
    rw [ssysCanonicalCode_eq, ssysCanonicalCode_eq, ← c9b5_sexprGodelEncode_eq,
      ← c9b5_sexprGodelEncode_eq]
    rfl

theorem primrec_ssysInterEqChar : Nat.Primrec ssysInterEqChar := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcanon : Nat.Primrec (fun n : ℕ => ssysCanonicalCode n) := by
    have := primrec_ssysActiveChar
    refine (Domain.Recursive.primrec_selectFn this Nat.Primrec.left
      (Nat.Primrec.const (SExpr.encode .sigma))).of_eq fun n => ?_
    unfold ssysCanonicalCode; rfl
  have hcn : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.1) := hcanon.comp hn
  have hcm : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.2.unpair.1) := hcanon.comp hm
  have hck : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.2.unpair.2) := hcanon.comp hk
  have hfuel : Nat.Primrec (fun t : ℕ =>
      t.unpair.1.unpair.2 + t.unpair.2.unpair.1.unpair.2 + t.unpair.2.unpair.2.unpair.2 + 3) :=
    Domain.Recursive.primrec_add₂
      (Domain.Recursive.primrec_add₂
        (Domain.Recursive.primrec_add₂
          (Nat.Primrec.right.comp hn) (Nat.Primrec.right.comp hm))
        (Nat.Primrec.right.comp hk))
      (Nat.Primrec.const 3)
  have hcap : Nat.Primrec (fun t : ℕ =>
      Domain.Recursive.capCode (ssysCanonicalCode t.unpair.1)
        (ssysCanonicalCode t.unpair.2.unpair.1)) := by
    have hp : Nat.Primrec (fun t : ℕ => Nat.pair 3 (Nat.pair (ssysCanonicalCode t.unpair.1)
        (ssysCanonicalCode t.unpair.2.unpair.1))) :=
      Nat.Primrec.pair (Nat.Primrec.const 3) (Nat.Primrec.pair hcn hcm)
    refine hp.of_eq fun t => ?_
    unfold Domain.Recursive.capCode; rfl
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair
      (t.unpair.1.unpair.2 + t.unpair.2.unpair.1.unpair.2 + t.unpair.2.unpair.2.unpair.2 + 3)
      (Nat.pair (Domain.Recursive.capCode (ssysCanonicalCode t.unpair.1)
          (ssysCanonicalCode t.unpair.2.unpair.1))
        (ssysCanonicalCode t.unpair.2.unpair.2))) :=
    Nat.Primrec.pair hfuel (Nat.Primrec.pair hcap hck)
  refine (Domain.Recursive.primrec_interEqChar.comp hpack).of_eq fun t => ?_
  unfold ssysInterEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem Ssys_interEq_computable :
    RecDecidable₃ (fun n m k => SsysX n ∩ SsysX m = SsysX k) :=
  RecDecidable₃.of_triple_zero_one_char primrec_ssysInterEqChar
    (fun t => by
      rcases (show ssysInterEqChar t = 0 ∨ ssysInterEqChar t = 1 from by
        have := ssysInterEqChar_le_one t; omega) with h | h <;> simp [h])
    (fun n m k => (ssysInterEqChar_eq_one_iff n m k).symm)

theorem Ssys_partially_effectively_given : PartiallyEffectivelyGiven Ssys := ⟨⟨SsysPres⟩⟩

end

end Exercise722
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise722
section
set_option linter.unusedVariables false

theorem example_722_presentation : Domain.Recursive.RecDecidable₃ fun (n m k : Nat) =>
  @Eq (Set (List Bool))
    (@Inter.inter (Set (List Bool)) (@Set.instInter (List Bool)) (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX n)
      (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX m))
    (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX k) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.Ssys_interEq_computable
end

end DomainTheory.NeighbourhoodSystems.Exercise722
namespace DomainTheory.NeighbourhoodSystems
namespace Exercise718
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β : Type*}

namespace EffectiveIso

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

def toDomainIso (e : EffectiveIso P Q) : DomainIso V W where
  toFun := e.toMap.toElementMap
  invFun := e.invMap.toElementMap
  left_inv x := by
    rw [← toElementMap_comp, e.left_inv, toElementMap_idMap]
  right_inv y := by
    rw [← toElementMap_comp, e.right_inv, toElementMap_idMap]
  map_rel_iff' := by
    intro x y
    show e.toMap.toElementMap x ≤ e.toMap.toElementMap y ↔ x ≤ y
    refine ⟨fun h => ?_, fun h => e.toMap.toElementMap_mono h⟩
    have hmono := e.invMap.toElementMap_mono h
    rwa [← toElementMap_comp, ← toElementMap_comp, e.left_inv, toElementMap_idMap,
      toElementMap_idMap] at hmono

end EffectiveIso
end

section
variable {α β : Type*}

namespace EffectiveIso

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

end EffectiveIso

theorem EffectivelyIsomorphic.isomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {P : ComputablePresentation V} {Q : ComputablePresentation W}
    (h : EffectivelyIsomorphic P Q) : V ≅ᴰ W :=
  h.elim fun e => ⟨e.toDomainIso⟩

variable {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

variable {P}

theorem iterSys_effectivelyIsomorphic_iterIter (P : ComputablePresentation V) :
    EffectivelyIsomorphic (iterPresentation P) (iterPresentation (iterPresentation P)) :=
  ⟨iterIterEffectiveIso P⟩

theorem iterSys_isomorphic_iterIter (P : ComputablePresentation V) :
    iterSys V ≅ᴰ iterSys (iterSys V) :=
  (iterSys_effectivelyIsomorphic_iterIter P).isomorphic
end

end Exercise718
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise718
section
set_option linter.unusedVariables false

theorem example_718.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
  @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic (Prod Nat α) (Prod Nat (Prod Nat α))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V)
    (@DomainTheory.NeighbourhoodSystems.iterSys (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (@DomainTheory.NeighbourhoodSystems.iterPresentation α V P)
    (@DomainTheory.NeighbourhoodSystems.iterPresentation (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
      (@DomainTheory.NeighbourhoodSystems.iterPresentation α V P)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise718.iterSys_effectivelyIsomorphic_iterIter
end

end DomainTheory.NeighbourhoodSystems.Exercise718
end
