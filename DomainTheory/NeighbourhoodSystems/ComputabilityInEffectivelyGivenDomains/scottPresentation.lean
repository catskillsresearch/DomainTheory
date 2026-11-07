module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive IndefProduct ApproximableMap

section
variable {α β γ : Type*}

structure ScottPresentation (V : NeighborhoodSystem α) where

  X : ℕ → Set α

  mem_X : ∀ n, V.mem (X n)

  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y

  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)

  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

class ComputableMapS {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ScottPresentation V) (Q : ScottPresentation W) (f : ApproximableMap V W) : Prop where
  out : REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

def NeighborhoodSystem.IsEffectivelyGivenS (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ScottPresentation V)

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

def inclShuffle (t : ℕ) : ℕ := Nat.pair t.unpair.1 (Nat.pair t.unpair.2 t.unpair.1)

theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)

theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

end ScottPresentation

end

section
variable {α β γ : Type*}

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff

end ScottPresentation
end

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

variable {α β γ : Type*}

def ComputablePresentation.toScott {V : NeighborhoodSystem α} (P : ComputablePresentation V) :
    ScottPresentation V where
  X := P.X
  mem_X := P.mem_X
  surj := P.surj
  interEq_computable := P.interEq_computable
  cons_computable := P.cons_computable

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

end ScottPresentation

section
variable {α β γ : Type*}

theorem NeighborhoodSystem.IsEffectivelyGiven.toS {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.IsEffectivelyGivenS :=
  h.elim fun P => ⟨P.toScott⟩

open SmashProduct








end
end DomainTheory.NeighbourhoodSystems
