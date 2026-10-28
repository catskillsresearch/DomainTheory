module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_24
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_13

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.subApprox
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Yseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

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

set_option linter.unusedVariables false

theorem theorem_86.{u} : And
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
        (@DomainTheory.NeighbourhoodSystems.subApprox α E)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.subApprox α E)) :=
  @And.intro
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
        (@DomainTheory.NeighbourhoodSystems.subApprox α E)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.subApprox α E))
  (@And.intro
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.subApprox α E))
    @DomainTheory.NeighbourhoodSystems.sub_eq_self_iff_isFinitaryProjection
    @DomainTheory.NeighbourhoodSystems.subApprox.isFinitary)
  @DomainTheory.NeighbourhoodSystems.Sub8_6.isFinitaryProjection_subApprox

set_option linter.unusedVariables false

theorem theorem_86_c.{u_1} : And
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E) (gN : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.stepFun α α E E
              (@DomainTheory.NeighbourhoodSystems.funListOf α α E E P P (Domain.Recursive.decodeList c)))))
    (incl eq : Nat → Nat) (hgNp : Nat.Primrec gN)
    (hincl :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hinclp : Nat.Primrec incl)
    (heq :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heqp : Nat.Primrec eq),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.subApprox α E))
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α E →
      ∃ (Pfun :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
        @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
          Pfun Pfun (@DomainTheory.NeighbourhoodSystems.subApprox α E)) :=
  @And.intro
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E) (gN : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.stepFun α α E E
              (@DomainTheory.NeighbourhoodSystems.funListOf α α E E P P (Domain.Recursive.decodeList c)))))
    (incl eq : Nat → Nat) (hgNp : Nat.Primrec gN)
    (hincl :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hinclp : Nat.Primrec incl)
    (heq :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heqp : Nat.Primrec eq),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.subApprox α E))
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α E →
      ∃ (Pfun :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
        @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
          Pfun Pfun (@DomainTheory.NeighbourhoodSystems.subApprox α E))
  @DomainTheory.NeighbourhoodSystems.subApprox_isComputable
  @DomainTheory.NeighbourhoodSystems.sub_isComputable_of_isEffectivelyGiven

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

def idxSet (n : ℕ) : Set ℕ := {m | e m ⊆ e n}

@[simp] theorem mem_idxSet {m n : ℕ} : m ∈ idxSet e n ↔ e m ⊆ e n := Iff.rfl

end Reencode

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in

theorem D_mem_e (n : ℕ) : D.mem (e n) := (hcover (e n)).mpr ⟨n, rfl⟩

noncomputable abbrev Yidx (n : ℕ) : Set ℚ := Yseq splitChoice (idxSet e) Set.univ n

include hcover in
theorem e_subset_master (n : ℕ) : e n ⊆ D.master := D.sub_master (D_mem_e D e hcover n)

end Setup

section Reencode

variable (e : ℕ → Set α)

theorem idxSet_inter_of_inter_eq {i j m : ℕ} (h : e i ∩ e j = e m) :
    idxSet e i ∩ idxSet e j = idxSet e m := by
  ext k
  show e k ⊆ e i ∧ e k ⊆ e j ↔ e k ⊆ e m
  rw [← Set.subset_inter_iff, h]

theorem idxSet_zero_eq_univ {n0 : ℕ} (hsub : ∀ m, e m ⊆ e n0) : idxSet e n0 = Set.univ :=
  Set.eq_univ_of_forall hsub

end Reencode

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover he0 in
theorem idxSet_zero : idxSet e 0 = Set.univ :=
  idxSet_zero_eq_univ e (fun m => he0 ▸ e_subset_master D e hcover m)

end Setup

section Reencode

variable (e : ℕ → Set α)

theorem self_mem_idxSet (n : ℕ) : n ∈ idxSet e n := show e n ⊆ e n from subset_rfl

theorem idxSet_subset_iff (i j : ℕ) : idxSet e i ⊆ idxSet e j ↔ e i ⊆ e j :=
  ⟨fun h => h (self_mem_idxSet e i), fun h _ hm => hm.trans h⟩

end Reencode

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

theorem univ_nonempty_nat : (Set.univ : Set ℕ).Nonempty := ⟨0, trivial⟩

theorem Yidx_empty_or_mem (n : ℕ) : Yidx e n = ∅ ∨ U.mem (Yidx e n) :=
  Yseq_empty_or_mem splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec n

theorem Yidx_nonempty (n : ℕ) : (Yidx e n).Nonempty :=
  Yseq_nonempty_of_mem splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec
    (Set.mem_univ n) (self_mem_idxSet e n)

theorem Yidx_mem (n : ℕ) : U.mem (Yidx e n) :=
  (Yidx_empty_or_mem e n).resolve_left (Yidx_nonempty e n).ne_empty

theorem Yidx_subset_master (n : ℕ) : Yidx e n ⊆ U.master :=
  Yseq_subset_master splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec n

include hcover he0 in

theorem Yidx_zero : Yidx e 0 = U.master :=
  Yseq_zero_eq_master splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec
    (idxSet_zero D e hcover he0)

theorem embed_subset_iff (i j : ℕ) : e i ⊆ e j ↔ Yidx e i ⊆ Yidx e j := by
  rw [← idxSet_subset_iff e i j]
  have := transfer_subset_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at this

theorem embed_eq_iff (i j : ℕ) : e i = e j ↔ Yidx e i = Yidx e j :=
  ⟨fun h => Set.Subset.antisymm ((embed_subset_iff e i j).mp h.subset)
      ((embed_subset_iff e j i).mp h.symm.subset),
    fun h => Set.Subset.antisymm ((embed_subset_iff e i j).mpr h.subset)
      ((embed_subset_iff e j i).mpr h.symm.subset)⟩

end Setup

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in

theorem exists_inter_index_of_dmem {i j : ℕ} (hDij : D.mem (e i ∩ e j)) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  obtain ⟨m, hm⟩ := (hcover (e i ∩ e j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec i j m
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp (idxSet_inter_of_inter_eq e hm)⟩

noncomputable def DprimeU : NeighborhoodSystem ℚ where
  mem Y := ∃ n, Y = Yidx e n
  master := U.master
  master_nonempty := U.master_nonempty
  master_mem := ⟨0, (Yidx_zero D e hcover he0).symm⟩
  sub_master := by rintro Y ⟨n, rfl⟩; exact Yidx_subset_master e n
  inter_mem := by
    rintro X Y Z ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ hZsub
    have h1 : e k ⊆ e i := (embed_subset_iff e k i).mpr (hZsub.trans Set.inter_subset_left)
    have h2 : e k ⊆ e j := (embed_subset_iff e k j).mpr (hZsub.trans Set.inter_subset_right)
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_dmem D e hcover
      (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
        (Set.subset_inter h1 h2))
    exact ⟨m, hYeq⟩

include hcover in

theorem exists_inter_index_of_nonempty {i j : ℕ} (hne : (Yidx e i ∩ Yidx e j).Nonempty) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  have hne' : (idxSet e i ∩ idxSet e j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem D e hcover
    (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
      (Set.subset_inter hki hkj))

include hcover he0 in

theorem DprimeU_subsystem : DprimeU D e hcover he0 ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact Yidx_mem e n
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty D e hcover hUmem.2.1
    exact ⟨m, hYeq⟩

end Subsystem

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

def toD (y : (DprimeU D e hcover he0).Element) : D.Element where
  mem S := ∃ n, S = e n ∧ y.mem (Yidx e n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D e hcover n
  master_mem := ⟨0, he0.symm, by rw [Yidx_zero D e hcover he0]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeU D e hcover he0).mem (Yidx e i ∩ Yidx e j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty D e hcover
      ((DprimeU_subsystem D e hcover he0).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover T).mp hDT
    have hYij : Yidx e i ⊆ Yidx e j := (embed_subset_iff e i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

def toDprimeU (x : D.Element) : (DprimeU D e hcover he0).Element where
  mem Y := ∃ n, Y = Yidx e n ∧ x.mem (e n)
  sub := fun ⟨n, hn, _⟩ => ⟨n, hn⟩
  master_mem := ⟨0, (Yidx_zero D e hcover he0).symm, by rw [he0]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hem, hYeq⟩ :=
      exists_inter_index_of_dmem D e hcover (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hYeq, hem ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl⟩ hXY
    have heij : e i ⊆ e j := (embed_subset_iff e i j).mpr hXY
    exact ⟨j, rfl, x.up_mem hxi (D_mem_e D e hcover j) heij⟩

noncomputable def domainIso : DomainIso D (DprimeU D e hcover he0) where
  toFun := toDprimeU D e hcover he0
  invFun := toD D e hcover he0
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff e n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hxS)
      have hxn : x.mem (e n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeU D e hcover he0 x).mem (Yidx e n))
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

end Iso

section Reencode

variable (e : ℕ → Set α)

theorem idxSet_eq_iff (i j : ℕ) : idxSet e i = idxSet e j ↔ e i = e j :=
  ⟨fun h => Set.Subset.antisymm ((idxSet_subset_iff e i j).mp h.subset)
      ((idxSet_subset_iff e j i).mp h.symm.subset),
    fun h => by rw [idxSet, idxSet, h]⟩

theorem idxSet_nonempty (n : ℕ) : (idxSet e n).Nonempty := ⟨n, self_mem_idxSet e n⟩

end Reencode

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

theorem isomorphic_DprimeU : D ≅ᴰ DprimeU D e hcover he0 := ⟨domainIso D e hcover he0⟩

end Iso

end DomainTheory.NeighbourhoodSystems
