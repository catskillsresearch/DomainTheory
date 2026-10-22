module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_VdiffRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vdiff_iff_nonempty

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(i)-for-`\`, for `V`**: `Xₙ \ Xₘ = X_k` for some `k` is recursively decidable. -/
theorem V_diff_computable : RecDecidable₂ (fun n m => ∃ k, VX k = VX n \ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VdiffRaw t.unpair.1 t.unpair.2) := primrec_VdiffRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec_myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    have := myLevelSetNonempty_le_one (VdiffRaw t.unpair.1 t.unpair.2).unpair.1
      (VdiffRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    rw [unpair_pair_fst, unpair_pair_snd, Vdiff_iff_nonempty, ← levelSet_VdiffRaw,
      myLevelSetNonempty_eq_one_iff]

end DomainTheory.NeighbourhoodSystems
