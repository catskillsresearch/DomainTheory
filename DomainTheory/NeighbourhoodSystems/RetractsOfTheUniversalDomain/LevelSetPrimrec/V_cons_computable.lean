/-ai
Scott's consistency condition 7.1(ii) for V, the existence of an enumerated
neighbourhood contained in the intersection of two enumerated neighbourhoods, is
recursively decidable.

The raw intersection of an unpaired pair is primitive recursive, and so is the
nonemptiness test of its level and mask, by composing the primitive-recursive
nonemptiness test with the two projections of that code and simplifying the pairing. The
paired zero-one characteristic of this test decides the predicate. The test is at most
one, so arithmetic supplies the bound. For the decision equivalence, the pairing
projections, the reduction of consistency to nonemptiness of the intersection, the
realization of that intersection by the raw code, and the characterization of the
nonemptiness test are rewritten in turn.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_myLevelSetNonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myLevelSetNonempty_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.primrec_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_VinterRaw
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.Vcons_iff_nonempty_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **7.1(ii) for `V`**: consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable, via
`Vcons_iff_nonempty_inter` and `myLevelSetNonempty`. -/
theorem V_cons_computable : RecDecidable₂ (fun n m => ∃ k, VX k ⊆ VX n ∩ VX m) := by
  have hvr : Nat.Primrec (fun t : ℕ => VinterRaw t.unpair.1 t.unpair.2) := primrec_VinterRaw
  have hfprim : Nat.Primrec (fun t : ℕ => myLevelSetNonempty (VinterRaw t.unpair.1 t.unpair.2).unpair.1
      (VinterRaw t.unpair.1 t.unpair.2).unpair.2) :=
    (primrec_myLevelSetNonempty.comp ((Nat.Primrec.left.comp hvr).pair
      (Nat.Primrec.right.comp hvr))).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable₂.of_paired_zero_one_char hfprim ?_ ?_
  · intro t
    have := myLevelSetNonempty_le_one (VinterRaw t.unpair.1 t.unpair.2).unpair.1
      (VinterRaw t.unpair.1 t.unpair.2).unpair.2
    omega
  · intro n m
    rw [unpair_pair_fst, unpair_pair_snd, Vcons_iff_nonempty_inter, ← levelSet_VinterRaw,
      myLevelSetNonempty_eq_one_iff]

end DomainTheory.NeighbourhoodSystems
