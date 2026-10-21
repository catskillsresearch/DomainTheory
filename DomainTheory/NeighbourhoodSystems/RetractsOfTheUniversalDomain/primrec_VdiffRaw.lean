/-ai
The function sending a paired natural number to the raw difference of its two components is primitive recursive.

The canonical indices of the two components, their levels and masks, and the maximum of the levels are primitive recursive by composition with the pairing projections and the maximum. Each upsampled mask is primitive recursive by composing upsampling with the level, the common level, and the mask. Their and-not is primitive recursive by composing and-not with that pair, and pairing the common level with the result agrees with the raw difference by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_myAndNot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem primrec_VdiffRaw : Nat.Primrec (fun t => VdiffRaw t.unpair.1 t.unpair.2) := by
  have hcn : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.1) := primrec_canonIdx.comp Nat.Primrec.left
  have hcm : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.2) := primrec_canonIdx.comp Nat.Primrec.right
  have hk1 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.1).unpair.1) := Nat.Primrec.left.comp hcn
  have hm1 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.1).unpair.2) := Nat.Primrec.right.comp hcn
  have hk2 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2).unpair.1) := Nat.Primrec.left.comp hcm
  have hm2 : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2).unpair.2) := Nat.Primrec.right.comp hcm
  have hkJ : Nat.Primrec (fun t : ℕ => max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) :=
    primrec_max hk1 hk2
  have hup1 : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.1).unpair.1
      (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1)
      (canonIdx t.unpair.1).unpair.2) :=
    (primrec_myUpsample.comp (hk1.pair (hkJ.pair hm1))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hup2 : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.2).unpair.1
      (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1)
      (canonIdx t.unpair.2).unpair.2) :=
    (primrec_myUpsample.comp (hk2.pair (hkJ.pair hm2))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have handnot : Nat.Primrec (fun t : ℕ => myAndNot
      (myUpsample (canonIdx t.unpair.1).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.1).unpair.2)
      (myUpsample (canonIdx t.unpair.2).unpair.1
        (max (canonIdx t.unpair.1).unpair.1 (canonIdx t.unpair.2).unpair.1) (canonIdx t.unpair.2).unpair.2)) :=
    (primrec_myAndNot.comp (hup1.pair hup2)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (hkJ.pair handnot).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
