module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.primrec_ratLtCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLtCode_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.ratLtCode_eq_one_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive
















/-- **`<` on rational codes is recursively decidable.** Packaged as `RecDecidable₂` (rather than the
raw `{0,1}` characteristic `ratLtCode`) so it composes directly with `Recursive.lean`'s closure
lemmas (`.not`, `.and`, `.bExistsList`, `.swap`, ...). -/
theorem ratLtCode_recDecidable₂ : RecDecidable₂ (fun c1 c2 => decodeRat c1 < decodeRat c2) := by
  refine RecDecidable₂.of_paired_zero_one_char primrec_ratLtCode
    (fun t => by have := ratLtCode_le_one t; omega) (fun n m => ?_)
  exact (ratLtCode_eq_one_iff n m).symm

end DomainTheory.NeighbourhoodSystems
