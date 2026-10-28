module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1
public import Mathlib.Order.BourbakiWitt

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise713
open NeighborhoodSystem Domain.Recursive

structure InclStructure where

  INCL : ℕ → ℕ → Prop

  meetIdx : ℕ → ℕ → ℕ

  topIdx : ℕ

  incl_dec : RecDecidable₂ INCL

  cons_dec : RecDecidable₂ (fun n m => ∃ k, INCL k n ∧ INCL k m)

  meet_dec : RecDecidable₃ (fun n m k => ∀ j, INCL j k ↔ (INCL j n ∧ INCL j m))

  meetIdx_primrec : Nat.Primrec (fun t => meetIdx t.unpair.1 t.unpair.2)

  incl_refl : ∀ n, INCL n n

  incl_trans : ∀ {n m k}, INCL n m → INCL m k → INCL n k

  topIdx_spec : ∀ n, INCL n topIdx

  meetIdx_spec : ∀ {n m}, (∃ k, INCL k n ∧ INCL k m) →
    ∀ j, INCL j (meetIdx n m) ↔ (INCL j n ∧ INCL j m)

end DomainTheory.NeighbourhoodSystems.Exercise713
end

section
namespace DomainTheory.NeighbourhoodSystems.Exercise713
open NeighborhoodSystem Domain.Recursive

section
namespace InclStructure

variable (I : InclStructure)

def CONS (n m : ℕ) : Prop := ∃ k, I.INCL k n ∧ I.INCL k m

def MEET (n m k : ℕ) : Prop := ∀ j, I.INCL j k ↔ (I.INCL j n ∧ I.INCL j m)

def toNbhd (n : ℕ) : Set ℕ := {m | I.INCL m n}

@[simp] theorem mem_toNbhd {n m : ℕ} : m ∈ I.toNbhd n ↔ I.INCL m n := Iff.rfl

theorem toNbhd_inter_eq_iff (n m k : ℕ) :
    I.toNbhd n ∩ I.toNbhd m = I.toNbhd k ↔ I.MEET n m k := by
  unfold MEET
  rw [Set.ext_iff]
  refine forall_congr' fun j => ?_
  rw [Set.mem_inter_iff, mem_toNbhd, mem_toNbhd, mem_toNbhd]
  exact iff_comm

theorem toNbhd_subset_iff {n k : ℕ} : I.toNbhd n ⊆ I.toNbhd k ↔ I.INCL n k := by
  constructor
  · intro h
    exact h (I.incl_refl n)
  · intro hnk m hm
    exact I.incl_trans hm hnk

theorem toNbhd_subset_inter_iff (k n m : ℕ) :
    I.toNbhd k ⊆ I.toNbhd n ∩ I.toNbhd m ↔ (I.INCL k n ∧ I.INCL k m) := by
  rw [Set.subset_inter_iff, I.toNbhd_subset_iff, I.toNbhd_subset_iff]

theorem toNbhd_top : I.toNbhd I.topIdx = Set.univ := by
  ext m
  simp only [mem_toNbhd, Set.mem_univ, iff_true]
  exact I.topIdx_spec m

def toSystem : NeighborhoodSystem ℕ where
  mem Y := ∃ n, Y = I.toNbhd n
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := ⟨I.topIdx, I.toNbhd_top.symm⟩
  inter_mem := by
    rintro X Y Z ⟨n, rfl⟩ ⟨m, rfl⟩ ⟨l, rfl⟩ hZsub
    have hln : I.INCL l n := I.toNbhd_subset_iff.mp (hZsub.trans Set.inter_subset_left)
    have hlm : I.INCL l m := I.toNbhd_subset_iff.mp (hZsub.trans Set.inter_subset_right)
    exact ⟨I.meetIdx n m, (I.toNbhd_inter_eq_iff n m (I.meetIdx n m)).mpr
      (I.meetIdx_spec ⟨l, hln, hlm⟩)⟩
  sub_master := by rintro X _; exact Set.subset_univ X

@[simp] theorem toSystem_mem {Y : Set ℕ} : I.toSystem.mem Y ↔ ∃ n, Y = I.toNbhd n := Iff.rfl

end InclStructure
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

theorem meet_iff_interEq (P : ComputablePresentation V) (n m k : ℕ) :
    (∀ j, P.X j ⊆ P.X k ↔ (P.X j ⊆ P.X n ∧ P.X j ⊆ P.X m)) ↔ (P.X n ∩ P.X m = P.X k) := by
  constructor
  · intro h
    have hk : P.X k ⊆ P.X n ∩ P.X m :=
      Set.subset_inter ((h k).mp subset_rfl).1 ((h k).mp subset_rfl).2
    refine Set.Subset.antisymm ?_ hk
    have hmem : V.mem (P.X n ∩ P.X m) := V.inter_mem (P.mem_X n) (P.mem_X m) (P.mem_X k) hk
    obtain ⟨p, hp⟩ := P.surj hmem
    have hpk : P.X p ⊆ P.X k :=
      (h p).mpr (by rw [hp]; exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩)
    exact hp ▸ hpk
  · intro h j
    rw [← h, Set.subset_inter_iff]

def ofPresentation (P : ComputablePresentation V) : InclStructure where
  INCL n m := P.X n ⊆ P.X m
  meetIdx := P.inter
  topIdx := P.masterIdx
  incl_dec := P.incl_computable
  cons_dec :=
    RecDecidable.of_iff
      (fun t => by
        refine exists_congr fun k => ?_
        exact (Set.subset_inter_iff).symm)
      P.cons_computable
  meet_dec :=
    RecDecidable.of_iff
      (fun t => meet_iff_interEq P t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
      P.interEq_computable
  meetIdx_primrec := P.inter_primrec
  incl_refl := fun _ => subset_rfl
  incl_trans := fun h1 h2 => h1.trans h2
  topIdx_spec := by
    intro n
    show P.X n ⊆ P.X P.masterIdx
    rw [P.masterIdx_spec]
    exact V.sub_master (P.mem_X n)
  meetIdx_spec := by
    intro n m hcons j
    obtain ⟨k, h1, h2⟩ := hcons
    have hcons' : ∃ k, P.X k ⊆ P.X n ∩ P.X m := ⟨k, Set.subset_inter h1 h2⟩
    show P.X j ⊆ P.X (P.inter n m) ↔ _
    rw [P.inter_spec hcons', Set.subset_inter_iff]

@[simp] theorem ofPresentation_INCL (P : ComputablePresentation V) (n m : ℕ) :
    (ofPresentation P).INCL n m ↔ P.X n ⊆ P.X m := Iff.rfl

@[simp] theorem mem_ofPresentation_toNbhd (P : ComputablePresentation V) (j n : ℕ) :
    j ∈ (ofPresentation P).toNbhd n ↔ P.X j ⊆ P.X n := Iff.rfl

theorem ofPresentation_toNbhd_eq_iff (P : ComputablePresentation V) (n m : ℕ) :
    (ofPresentation P).toNbhd n = (ofPresentation P).toNbhd m ↔ P.X n = P.X m := by
  rw [Set.Subset.antisymm_iff, (ofPresentation P).toNbhd_subset_iff,
    (ofPresentation P).toNbhd_subset_iff]
  show (P.X n ⊆ P.X m ∧ P.X m ⊆ P.X n) ↔ P.X n = P.X m
  exact (Set.Subset.antisymm_iff).symm

abbrev reconstruct (P : ComputablePresentation V) : NeighborhoodSystem ℕ :=
  (ofPresentation P).toSystem

def reconElem (P : ComputablePresentation V) (x : V.Element) : (reconstruct P).Element where
  mem Y := ∃ n, Y = (ofPresentation P).toNbhd n ∧ x.mem (P.X n)
  sub := by rintro Y ⟨n, rfl, _⟩; exact ⟨n, rfl⟩
  master_mem :=
    ⟨P.masterIdx, (ofPresentation P).toNbhd_top.symm, by rw [P.masterIdx_spec]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, rfl, hxn⟩ ⟨m, rfl, hxm⟩
    have hmem : V.mem (P.X n ∩ P.X m) := x.sub (x.inter_mem hxn hxm)
    obtain ⟨q, hq⟩ := P.surj hmem
    refine ⟨q, ?_, ?_⟩
    · ext j
      rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd,
        mem_ofPresentation_toNbhd, hq, Set.subset_inter_iff]
    · have : x.mem (P.X q) := by rw [hq]; exact x.inter_mem hxn hxm
      exact this
  up_mem := by
    rintro X Y ⟨n, rfl, hxn⟩ ⟨m, rfl⟩ hsub
    have hnm : P.X n ⊆ P.X m := (ofPresentation P).toNbhd_subset_iff.mp hsub
    exact ⟨m, rfl, x.up_mem hxn (P.mem_X m) hnm⟩

def reconElemInv (P : ComputablePresentation V) (y : (reconstruct P).Element) : V.Element where
  mem W := ∃ n, W = P.X n ∧ y.mem ((ofPresentation P).toNbhd n)
  sub := by rintro W ⟨n, rfl, _⟩; exact P.mem_X n
  master_mem :=
    ⟨P.masterIdx, P.masterIdx_spec.symm, by
      rw [show (ofPresentation P).toNbhd P.masterIdx = Set.univ from (ofPresentation P).toNbhd_top]
      exact y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, rfl, hyn⟩ ⟨m, rfl, hym⟩
    obtain ⟨p, hp⟩ := y.sub (y.inter_mem hyn hym)
    have hpmem : p ∈ (ofPresentation P).toNbhd n ∩ (ofPresentation P).toNbhd m :=
      hp ▸ ((ofPresentation P).mem_toNbhd.mpr ((ofPresentation P).incl_refl p))
    rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd] at hpmem
    have hwit : P.X p ⊆ P.X n ∩ P.X m := Set.subset_inter hpmem.1 hpmem.2
    have hmem : V.mem (P.X n ∩ P.X m) := V.inter_mem (P.mem_X n) (P.mem_X m) (P.mem_X p) hwit
    obtain ⟨q, hq⟩ := P.surj hmem
    refine ⟨q, hq.symm, ?_⟩
    have htoNbhd : (ofPresentation P).toNbhd q
        = (ofPresentation P).toNbhd n ∩ (ofPresentation P).toNbhd m := by
      ext j
      rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd,
        mem_ofPresentation_toNbhd, hq, Set.subset_inter_iff]
    rw [htoNbhd]
    exact y.inter_mem hyn hym
  up_mem := by
    rintro W Z ⟨n, rfl, hyn⟩ hZ hWZ
    obtain ⟨p, hp⟩ := P.surj hZ
    refine ⟨p, hp.symm, ?_⟩
    have hnp : (ofPresentation P).toNbhd n ⊆ (ofPresentation P).toNbhd p :=
      (ofPresentation P).toNbhd_subset_iff.mpr (by show P.X n ⊆ P.X p; rw [hp]; exact hWZ)
    exact y.up_mem hyn ⟨p, rfl⟩ hnp

def reconIso (P : ComputablePresentation V) : V.Element ≃o (reconstruct P).Element where
  toFun := reconElem P
  invFun := reconElemInv P
  left_inv := by
    intro x
    apply Element.ext
    intro W
    constructor
    · rintro ⟨n, rfl, m, hWm, hxm⟩
      rw [ofPresentation_toNbhd_eq_iff] at hWm
      rw [hWm]; exact hxm
    · intro hxW
      obtain ⟨n, hn⟩ := P.surj (x.sub hxW)
      exact ⟨n, hn.symm, n, rfl, by rw [hn]; exact hxW⟩
  right_inv := by
    intro y
    apply Element.ext
    intro T
    constructor
    · rintro ⟨n, rfl, m, hXm, hym⟩
      have : (ofPresentation P).toNbhd n = (ofPresentation P).toNbhd m :=
        (ofPresentation_toNbhd_eq_iff P n m).mpr hXm
      rw [this]; exact hym
    · intro hyT
      obtain ⟨n, hn⟩ := y.sub hyT
      exact ⟨n, hn, n, rfl, by rw [← hn]; exact hyT⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hxW
      obtain ⟨n, hn⟩ := P.surj (x.sub hxW)
      have hmem : (reconElem P x).mem ((ofPresentation P).toNbhd n) :=
        ⟨n, rfl, by rw [hn]; exact hxW⟩
      obtain ⟨m, hm, hx'm⟩ := h ((ofPresentation P).toNbhd n) hmem
      rw [ofPresentation_toNbhd_eq_iff] at hm
      rw [← hn, hm]; exact hx'm
    · intro h Y hY
      obtain ⟨n, rfl, hxn⟩ := hY
      exact ⟨n, rfl, h (P.X n) hxn⟩

end

section
namespace InclStructure

variable (I : InclStructure)

def toPresentation : ComputablePresentation I.toSystem where
  X := I.toNbhd
  mem_X n := ⟨n, rfl⟩
  surj := by rintro Y ⟨n, rfl⟩; exact ⟨n, rfl⟩
  interEq_computable :=
    RecDecidable.of_iff
      (fun t => (I.toNbhd_inter_eq_iff t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2))
      I.meet_dec
  cons_computable :=
    RecDecidable.of_iff
      (fun t => by
        refine exists_congr fun k => ?_
        exact I.toNbhd_subset_inter_iff k t.unpair.1 t.unpair.2)
      I.cons_dec
  inter := I.meetIdx
  inter_primrec := I.meetIdx_primrec
  inter_spec := by
    intro n m hcons
    obtain ⟨k, hk⟩ := hcons
    rw [Set.subset_inter_iff] at hk
    have hcons' : I.CONS n m := ⟨k, I.toNbhd_subset_iff.mp hk.1, I.toNbhd_subset_iff.mp hk.2⟩
    exact ((I.toNbhd_inter_eq_iff n m (I.meetIdx n m)).mpr (I.meetIdx_spec hcons')).symm
  masterIdx := I.topIdx
  masterIdx_spec := I.toNbhd_top

theorem axiom_i (n : ℕ) : I.INCL n n := I.incl_refl n

theorem axiom_ii {n m k : ℕ} (h1 : I.INCL n m) (h2 : I.INCL m k) : I.INCL n k := I.incl_trans h1 h2

theorem axiom_iii : ∃ m, ∀ n, I.INCL n m := ⟨I.topIdx, I.topIdx_spec⟩

theorem axiom_iv (n m : ℕ) (h : I.CONS n m) : ∃ k, I.MEET n m k :=
  ⟨I.meetIdx n m, I.meetIdx_spec h⟩

end InclStructure
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

theorem ofPresentation_toPresentation_INCL (I : InclStructure) (n m : ℕ) :
    (ofPresentation I.toPresentation).INCL n m ↔ I.INCL n m := by
  show I.toNbhd n ⊆ I.toNbhd m ↔ I.INCL n m
  exact I.toNbhd_subset_iff

theorem reconstruct_isomorphic (P : ComputablePresentation V) : reconstruct P ≅ᴰ V :=
  ⟨(reconIso P).symm⟩

end

section
namespace InclStructure

variable (I : InclStructure)

theorem toSystem_isEffectivelyGiven : I.toSystem.IsEffectivelyGiven := ⟨I.toPresentation⟩

end InclStructure
end

section
set_option linter.unusedVariables false

theorem example_713.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
    @DomainTheory.NeighbourhoodSystems.Isomorphic Nat α
      (@DomainTheory.NeighbourhoodSystems.Exercise713.reconstruct α V P) V)
  (∀ (I : DomainTheory.NeighbourhoodSystems.Exercise713.InclStructure),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven Nat I.toSystem) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
    @DomainTheory.NeighbourhoodSystems.Isomorphic Nat α
      (@DomainTheory.NeighbourhoodSystems.Exercise713.reconstruct α V P) V)
  (∀ (I : DomainTheory.NeighbourhoodSystems.Exercise713.InclStructure),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven Nat I.toSystem)
  (@DomainTheory.NeighbourhoodSystems.Exercise713.reconstruct_isomorphic)
  DomainTheory.NeighbourhoodSystems.Exercise713.InclStructure.toSystem_isEffectivelyGiven
end

end DomainTheory.NeighbourhoodSystems.Exercise713
end
