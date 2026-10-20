module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.affine_eq_biInter

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem











theorem generatedBy_affine (k ℓ : ℕ) (hℓ : ℓ < 2 ^ k) : GeneratedBy generator (affine k ℓ) := by
  rw [affine_eq_biInter k ℓ hℓ]
  induction Finset.range k using Finset.induction_on with
  | empty => simpa using GeneratedBy.univ
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    refine GeneratedBy.inter ?_ ih
    split_ifs with hb
    · exact GeneratedBy.of _
    · exact GeneratedBy.compl (GeneratedBy.of _)

end DomainTheory.NeighbourhoodSystems
