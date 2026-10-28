module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_1

public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example78
open Domain.Recursive NeighborhoodSystem

section

def nbhd (n : ℕ) : Set ℕ := {k | n.testBit k = false}
end

section
@[simp] theorem mem_nbhd {n k : ℕ} : k ∈ nbhd n ↔ n.testBit k = false := Iff.rfl
end

section

theorem nbhd_injective {n m : ℕ} (h : nbhd n = nbhd m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hk : (n.testBit k = false) ↔ (m.testBit k = false) := by
    have := Set.ext_iff.mp h k; simpa only [mem_nbhd] using this
  cases hn : n.testBit k <;> cases hm : m.testBit k <;> simp_all
end

section

theorem nbhd_inter (n m : ℕ) : nbhd n ∩ nbhd m = nbhd (myLor n m) := by
  ext k
  simp only [nbhd, Set.mem_inter_iff, Set.mem_ofPred_eq, myLor_eq_lor, Nat.testBit_lor,
    Bool.or_eq_false_iff]
end

section

theorem nbhd_zero : nbhd 0 = Set.univ := by
  ext k; simp [nbhd, Nat.zero_testBit]
end

section

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

end DomainTheory.NeighbourhoodSystems.Example78

section
namespace DomainTheory.NeighbourhoodSystems.Example78
open Domain.Recursive NeighborhoodSystem
section

def PNpres : ComputablePresentation PN where
  X := nbhd
  mem_X n := ⟨n, rfl⟩
  surj := by rintro Y ⟨n, rfl⟩; exact ⟨n, rfl⟩
  interEq_computable := by

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

theorem PN_consistent (n m : ℕ) : ∃ k, nbhd k ⊆ nbhd n ∩ nbhd m :=
  ⟨myLor n m, (nbhd_inter n m).symm.subset⟩
end

section

theorem PN_isEffectivelyGiven : PN.IsEffectivelyGiven := ⟨PNpres⟩
end

end DomainTheory.NeighbourhoodSystems.Example78
end
