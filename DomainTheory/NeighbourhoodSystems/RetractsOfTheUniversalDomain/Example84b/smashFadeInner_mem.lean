module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


section Smash


theorem smashFadeInner_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashFadeInner.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧ (Z = (prod D E).master ∨ (z.snd ≠ E.bot ∧ z.mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁,
    toElementMap_idMap, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

end Smash
end DomainTheory.NeighbourhoodSystems
