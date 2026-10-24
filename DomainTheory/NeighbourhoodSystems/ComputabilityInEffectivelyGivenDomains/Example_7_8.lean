module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

public import Mathlib.Data.Nat.Bitwise

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example78
open Domain.Recursive NeighborhoodSystem

section
/-- The neighbourhood `ℕ ∖ Eₙ` of the powerset domain: the cofinite set of bit positions **not**
set in `n`. Scott's `Eₙ` is `{k ∣ n.testBit k}`, so `nbhd n = {k ∣ n.testBit k = false}`. -/
def nbhd (n : ℕ) : Set ℕ := {k | n.testBit k = false}
end

section
@[simp] theorem mem_nbhd {n k : ℕ} : k ∈ nbhd n ↔ n.testBit k = false := Iff.rfl
end

section
/-- The enumeration `n ↦ nbhd n` is **one-one** (Scott's converse-ordered neighbourhoods are in
bijection with the indices): from `nbhd n = nbhd m` we recover `n = m` bit by bit. -/
theorem nbhd_injective {n m : ℕ} (h : nbhd n = nbhd m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hk : (n.testBit k = false) ↔ (m.testBit k = false) := by
    have := Set.ext_iff.mp h k; simpa only [mem_nbhd] using this
  cases hn : n.testBit k <;> cases hm : m.testBit k <;> simp_all
end

section
/-- **Scott's `Eₙ ∪ Eₘ = E_{n ||| m}`.** The intersection of two cofinite neighbourhoods is again
one: `nbhd n ∩ nbhd m = nbhd (n ||| m)` (bitwise OR of the excluded finite sets). -/
theorem nbhd_inter (n m : ℕ) : nbhd n ∩ nbhd m = nbhd (myLor n m) := by
  ext k
  simp only [nbhd, Set.mem_inter_iff, Set.mem_ofPred_eq, myLor_eq_lor, Nat.testBit_lor,
    Bool.or_eq_false_iff]
end

section
/-- `nbhd 0 = ℕ = Δ`: `0` has no set bits, so its excluded set `E₀` is empty. -/
theorem nbhd_zero : nbhd 0 = Set.univ := by
  ext k; simp [nbhd, Nat.zero_testBit]
end

section
/-- **The powerset domain `PN`** as a neighbourhood system over the token type `ℕ`: the
neighbourhoods are the cofinite sets `nbhd n`, with master `Δ = ℕ`. Closure under intersection is
`nbhd_inter` (the intersection is `nbhd (n ||| m)`), so no consistency hypothesis is even needed. -/
def PN : NeighborhoodSystem ℕ where
  mem Y := ∃ n, Y = nbhd n
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := ⟨0, nbhd_zero.symm⟩
  inter_mem := by
    rintro X Y Z ⟨a, rfl⟩ ⟨b, rfl⟩ _ _
    exact ⟨myLor a b, nbhd_inter a b⟩
  sub_master := by rintro X _; exact Set.subset_univ X
end

section
end
end DomainTheory.NeighbourhoodSystems.Example78

section
namespace DomainTheory.NeighbourhoodSystems.Example78
open Domain.Recursive NeighborhoodSystem
section
/- concordance: source L4477 EXAMPLE 7.8 powerset effectively given -/
/-- **Example 7.8 — the computable presentation of `PN`.** The enumeration is `nbhd`; the
intersection function is the choice-free primitive-recursive bitwise OR `myLor`; Scott's relation
7.1(i) is `nbhd n ∩ nbhd m = nbhd k ↔ (n ||| m) = k`, decided by `RecDecidable.natEq`; relation
7.1(ii) (consistency) is always true. -/
def PNpres : ComputablePresentation PN where
  X := nbhd
  mem_X n := ⟨n, rfl⟩
  surj := by rintro Y ⟨n, rfl⟩; exact ⟨n, rfl⟩
  interEq_computable := by
    -- `nbhd n ∩ nbhd m = nbhd k ↔ myLor n m = k`, an equality of two primitive-recursive functions
    refine RecDecidable.of_iff (q := fun t =>
        nbhd t.unpair.1 ∩ nbhd t.unpair.2.unpair.1 = nbhd t.unpair.2.unpair.2)
      (fun t => ?_)
      (RecDecidable.natEq
        (a := fun t => myLor t.unpair.1 t.unpair.2.unpair.1)
        (b := fun t => t.unpair.2.unpair.2)
        ((primrec_myLor.comp
          (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun s => by
            simp only [unpair_pair_fst, unpair_pair_snd])
        (Nat.Primrec.right.comp Nat.Primrec.right))
    -- the pointwise equivalence
    constructor
    · intro h; exact nbhd_injective ((nbhd_inter _ _).symm.trans h)
    · intro h; rw [nbhd_inter]; exact congrArg nbhd h
  cons_computable :=
    recDecidable_of_forall fun t => ⟨myLor t.unpair.1 t.unpair.2, (nbhd_inter _ _).symm.subset⟩
  inter := myLor
  inter_primrec := primrec_myLor
  inter_spec := fun {n m} _ => (nbhd_inter n m).symm
  masterIdx := 0
  masterIdx_spec := nbhd_zero
end

section
/-- **Any two neighbourhoods of `PN` are consistent** (Scott: "any two neighbourhoods are
consistent"): their intersection `nbhd (n ||| m)` is itself a neighbourhood contained in both. -/
theorem PN_consistent (n m : ℕ) : ∃ k, nbhd k ⊆ nbhd n ∩ nbhd m :=
  ⟨myLor n m, (nbhd_inter n m).symm.subset⟩
end

section
/-- **Example 7.8 (Scott 1981, PRG-19).** The powerset domain `PN` is effectively given. -/
theorem PN_isEffectivelyGiven : PN.IsEffectivelyGiven := ⟨PNpres⟩
end

end DomainTheory.NeighbourhoodSystems.Example78
end

section
/- concordance: source L4607 EXERCISES — Lecture VII exercises -/
-- Exercise713/InclStructure.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

end DomainTheory.NeighbourhoodSystems.Exercise713
end
