/-ai
The list-indexed enumeration at a code equals the universal neighbourhood of the index chain of the enumerator's image of the decoded list.

The fold step unpacks to the universal intersection of the accumulator with the enumerator at the next entry. The fold-code equation, followed by folding after mapping, turns the raw index into that index chain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QstepFn
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'Xcode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.Q'X

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

/-- `Q'X r n` is `UX` at the `idxchain`-index of the `r`-image of `n`'s list — i.e. `Q'X r` really is
`Theorem75`'s generic `idxchain` fold, just specialized through `r`. -/
theorem Q'X_eq (r : ℕ → ℕ) (n : ℕ) :
    Q'X r n = UX (idxchain UComputablePresentation (List.map r (decodeList n))) := by
  have hstep : (fun (acc x : ℕ) => QstepFn r (Nat.pair x (Nat.pair acc 0)))
      = fun acc x => Uinter acc (r x) := by
    funext acc x; unfold QstepFn; simp only [unpair_pair_fst, unpair_pair_snd]
  unfold Q'X Q'Xcode idxchain
  rw [foldCode_eq', hstep, List.foldl_map]
  rfl

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
