module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.toElementMap_prodMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves identities: `I × I = I`. -/
theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]

end DomainTheory.NeighbourhoodSystems
