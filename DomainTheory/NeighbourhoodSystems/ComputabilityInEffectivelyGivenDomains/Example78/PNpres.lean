/-ai
The computable presentation of the powerset enumerates the cofinite neighbourhoods by their indices, and every neighbourhood arises in this way. Equality of an intersection of two enumerated neighbourhoods with a third is equivalent to equality of the bitwise disjunction of the first two indices with the third: neighbourhood equality and the intersection law give index equality by injectivity, and index equality gives neighbourhood equality by the intersection law. That index equality is recursively decidable as equality of primitive-recursive functions. Any two indices are consistent, witnessed by their bitwise disjunction, whose neighbourhood is their intersection. The intersection function is that primitive-recursive disjunction, and it specifies the intersection. The master index is zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.mem_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.nbhd_injective
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78.PN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems.Example78
