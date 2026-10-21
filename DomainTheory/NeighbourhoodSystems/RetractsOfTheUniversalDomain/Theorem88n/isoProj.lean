/-ai
The code-level projection is the approximable map from the coded copy back to the neighbourhood system obtained by applying the isomorphism construction of Theorem 2.7 to the inverse code-level domain isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`isoProj : D'' → D`**, Theorem 2.7 applied to the inverse iso. -/
noncomputable def isoProj : ApproximableMap (DprimeUCode P) D := ofIso (domainIsoCode P).symm

end DomainTheory.NeighbourhoodSystems
