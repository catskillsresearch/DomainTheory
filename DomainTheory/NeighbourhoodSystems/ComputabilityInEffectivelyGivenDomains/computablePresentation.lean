module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.rePred
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodIso

public import Mathlib.Computability.Primrec.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

section
variable {α : Type*}

structure ComputablePresentation (V : NeighborhoodSystem α) where

  X : ℕ → Set α

  mem_X : ∀ n, V.mem (X n)

  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y

  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)

  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

  inter : ℕ → ℕ → ℕ

  inter_primrec : Nat.Primrec (fun t => inter t.unpair.1 t.unpair.2)

  inter_spec : ∀ {n m : ℕ}, (∃ k, X k ⊆ X n ∩ X m) → X (inter n m) = X n ∩ X m

  masterIdx : ℕ

  masterIdx_spec : X masterIdx = V.master

def NeighborhoodSystem.IsEffectivelyGiven (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ComputablePresentation V)

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

def inclShuffle (t : ℕ) : ℕ := Nat.pair t.unpair.1 (Nat.pair t.unpair.2 t.unpair.1)

def reindexInvolutive (P : ComputablePresentation V) (φ : ℕ → ℕ)
    (hφinv : Function.Involutive φ) (hφp : Nat.Primrec φ) : ComputablePresentation V where
  X n := P.X (φ n)
  mem_X n := P.mem_X (φ n)
  surj := fun {Y} hY => by
    obtain ⟨k, hk⟩ := P.surj hY
    exact ⟨φ k, by rw [hφinv k]; exact hk⟩
  interEq_computable := by
    have hreindex : Nat.Primrec (fun t : ℕ =>
        Nat.pair (φ t.unpair.1) (Nat.pair (φ t.unpair.2.unpair.1) (φ t.unpair.2.unpair.2))) :=
      (hφp.comp Nat.Primrec.left).pair
        ((hφp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (hφp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp hreindex)
    simp only [unpair_pair_fst, unpair_pair_snd]
  cons_computable := by
    have hreindex : Nat.Primrec (fun t : ℕ =>
        Nat.pair (φ t.unpair.1) (φ t.unpair.2)) :=
      (hφp.comp Nat.Primrec.left).pair (hφp.comp Nat.Primrec.right)
    refine RecDecidable.of_iff (fun t => ?_) (P.cons_computable.comp hreindex)
    simp only [unpair_pair_fst, unpair_pair_snd]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨φ k, hk⟩
    · rintro ⟨k, hk⟩; exact ⟨φ k, by rwa [hφinv]⟩
  inter n m := φ (P.inter (φ n) (φ m))
  inter_primrec := by
    have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (φ t.unpair.1) (φ t.unpair.2)) :=
      (hφp.comp Nat.Primrec.left).pair (hφp.comp Nat.Primrec.right)
    exact (hφp.comp ((P.inter_primrec.comp hreindex))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  inter_spec {n m} h := by
    show P.X (φ (φ (P.inter (φ n) (φ m)))) = P.X (φ n) ∩ P.X (φ m)
    rw [hφinv]
    obtain ⟨k, hk⟩ := h
    exact P.inter_spec ⟨φ k, hk⟩
  masterIdx := φ P.masterIdx
  masterIdx_spec := by show P.X (φ (φ P.masterIdx)) = V.master; rw [hφinv]; exact P.masterIdx_spec

def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

end ComputablePresentation

end

section
variable {α : Type*}

def unitPresentation : ComputablePresentation unitSys where
  X _ := Set.univ
  mem_X _ := rfl
  surj := by rintro Y rfl; exact ⟨0, rfl⟩
  interEq_computable := recDecidable_of_forall fun _ => Set.inter_self Set.univ
  cons_computable := recDecidable_of_forall fun _ =>
    ⟨0, by rw [Set.inter_self]⟩
  inter _ _ := 0
  inter_primrec := Nat.Primrec.zero
  inter_spec _ := by rw [Set.inter_self]
  masterIdx := 0
  masterIdx_spec := rfl

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)

private theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff

end ComputablePresentation

end

section
variable {α : Type*}

theorem unitSys_isEffectivelyGiven : unitSys.IsEffectivelyGiven :=
  ⟨unitPresentation⟩
end

end DomainTheory.NeighbourhoodSystems
