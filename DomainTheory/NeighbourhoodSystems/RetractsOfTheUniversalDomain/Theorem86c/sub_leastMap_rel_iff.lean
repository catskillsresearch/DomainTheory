/-ai
The map sub of the least map of the enumerated neighbourhood of index n relates the presented neighbourhoods of a and b exactly when some index y has the enumerated neighbourhood of n contained in the enumerated neighbourhood of y paired with itself, and the presented neighbourhood of y lies between those of a and b.

The reindexed existential of sub rewrites the self-relation of the least map on a presented neighbourhood as that enumerated inclusion, by the relation of a least map on a code pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.sub_rel_iff_exists_index

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`sub` of `Xenum n`'s least map, in fully decidable-existential form.** Combines
`sub_rel_iff_exists_index` with Theorem 7.6's `leastMap_Xenum_rel`/`Xenum_codePair` to turn the
witness condition `ĝₙ.rel (X_y) (X_y)` into the recursively decidable function-space inclusion
`Xenum n ⊆ Xenum (codePair y y)`. -/
theorem sub_leastMap_rel_iff (n a b : ℕ) :
    (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
        (P.X a) (P.X b) ↔
      ∃ y : ℕ, Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel_iff_exists_index P]
  refine exists_congr (fun y => ?_)
  rw [leastMap_Xenum_rel P gN hgN n y y, Xenum_codePair P gN hgN y y]

end SubComputable
end DomainTheory.NeighbourhoodSystems
