/-ai
An effective isomorphism between two computable presentations consists of approximable maps in both directions, each computable, such that each composite is the identity map of the corresponding neighbourhood system.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- **Exercise 7.18 (Scott 1981, PRG-19) — effective isomorphism (completing the sentence).** Two
effectively given systems `D` (presentation `P`) and `E` (presentation `Q`) are *effectively
isomorphic* iff there is a pair of mutually inverse approximable maps `toMap : D → E`,
`invMap : E → D`, **both computable** (Definition 7.2). -/
structure EffectiveIso {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) where
  /-- The forward map `D → E`. -/
  toMap : ApproximableMap V W
  /-- The inverse map `E → D`. -/
  invMap : ApproximableMap W V
  /-- The forward map is computable. -/
  toMap_computable : ComputableMap P Q toMap
  /-- The inverse map is computable. -/
  invMap_computable : ComputableMap Q P invMap
  /-- `invMap ∘ toMap = I_D`. -/
  left_inv : invMap.comp toMap = idMap V
  /-- `toMap ∘ invMap = I_E`. -/
  right_inv : toMap.comp invMap = idMap W

end Exercise718
end DomainTheory.NeighbourhoodSystems
