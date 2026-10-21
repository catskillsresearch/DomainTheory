/-ai
The code-level injection is the approximable map from the neighbourhood system to its coded copy obtained by applying the isomorphism construction of Theorem 2.7 to the code-level domain isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_inj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_proj_isComputableMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88f.DprimeUCode_projectionPair_isComputable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **`isoInj : D → D''`**, Theorem 2.7 applied to `domainIsoCode P`. -/
noncomputable def isoInj : ApproximableMap D (DprimeUCode P) := ofIso (domainIsoCode P)

end DomainTheory.NeighbourhoodSystems
