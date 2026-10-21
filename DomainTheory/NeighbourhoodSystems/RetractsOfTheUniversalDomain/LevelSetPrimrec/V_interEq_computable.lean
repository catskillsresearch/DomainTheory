/-ai
Scott's relation 7.1(i) for V, equality of the intersection of two enumerated
neighbourhoods with a third, is recursively decidable.

Unfolding the three-argument decision predicate, the raw intersection of the first
component with the left half of the second, its level and mask, the canonicalization of
the right half of the second and that code's level and mask, and the maximum of the two
levels, are primitive recursive by the stated compositions, with the pairing projections
simplified where a composition is identified. The two upsamplings of the masks to that
joint level are primitive recursive in the same way. Equality of natural numbers decides
those two upsamplings. The decision equivalence rewrites by the realization of the
intersection by the raw code and by the reduction of level-set equality to equality of
the upsampled masks, after which the two sides agree by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_canonIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_eq_iff_myUpsample_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_VinterRaw

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i) for `V`**: `Xₙ ∩ Xₘ = X_k` is recursively decidable, reduced to `myUpsample` equality
of the raw intersection code against `X_k`'s own code (`levelSet_eq_iff_myUpsample_eq`). -/
theorem V_interEq_computable : RecDecidable₃ (fun n m k => VX n ∩ VX m = VX k) := by
  unfold RecDecidable₃
  have hvr : Nat.Primrec (fun t : ℕ => VinterRaw t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_VinterRaw.comp (Nat.Primrec.left.pair
      (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hvrK : Nat.Primrec (fun t : ℕ => (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1) :=
    Nat.Primrec.left.comp hvr
  have hvrM : Nat.Primrec (fun t : ℕ => (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.2) :=
    Nat.Primrec.right.comp hvr
  have hck : Nat.Primrec (fun t : ℕ => canonIdx t.unpair.2.unpair.2) :=
    primrec_canonIdx.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hckK : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2.unpair.2).unpair.1) :=
    Nat.Primrec.left.comp hck
  have hckM : Nat.Primrec (fun t : ℕ => (canonIdx t.unpair.2.unpair.2).unpair.2) :=
    Nat.Primrec.right.comp hck
  have hkJ : Nat.Primrec (fun t : ℕ =>
      max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1) :=
    primrec_max hvrK hckK
  have hLHS : Nat.Primrec (fun t : ℕ => myUpsample (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1
      (max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1)
      (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.2) :=
    (primrec_myUpsample.comp (hvrK.pair (hkJ.pair hvrM))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun t : ℕ => myUpsample (canonIdx t.unpair.2.unpair.2).unpair.1
      (max (VinterRaw t.unpair.1 t.unpair.2.unpair.1).unpair.1 (canonIdx t.unpair.2.unpair.2).unpair.1)
      (canonIdx t.unpair.2.unpair.2).unpair.2) :=
    (primrec_myUpsample.comp (hckK.pair (hkJ.pair hckM))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (RecDecidable.natEq hLHS hRHS)
  dsimp only
  rw [← levelSet_VinterRaw, ← levelSet_eq_iff_myUpsample_eq]
  rfl

end DomainTheory.NeighbourhoodSystems
