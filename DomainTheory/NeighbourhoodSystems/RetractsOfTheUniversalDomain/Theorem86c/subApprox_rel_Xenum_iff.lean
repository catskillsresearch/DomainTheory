module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86c.subApprox_rel_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}


section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`subApprox`'s relation, specialized to `Xenum`.** `(Xenum n) subApprox (Xenum m)` holds iff,
whenever `m` is consistent, `sub` of `Xenum n`'s least map relates every coded step of `Xenum m`. -/
theorem subApprox_rel_Xenum_iff (n m : ℕ) :
    (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m) ↔
      gN m = 1 → ∀ e ∈ decodeList m,
        (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
          (P.X e.unpair.1) (P.X e.unpair.2) := by
  rw [subApprox_rel_iff (Xenum_mem P P gN hgN n), and_iff_right (Xenum_mem P P gN hgN m)]
  exact mem_Xenum_iff_map P P gN _ m

end SubComputable
end DomainTheory.NeighbourhoodSystems
