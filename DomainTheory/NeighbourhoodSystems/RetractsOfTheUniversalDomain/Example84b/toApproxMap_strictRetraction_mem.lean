module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.mem_toElementMap_fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.check_toElementMap_mem_zero_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_snd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictEvalFade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.strictRetraction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- The closed form of `strict`'s elementwise action: `strict(f)(y) = ⊥_E` if `y = ⊥_D`, else
`f(y)`. -/
theorem toApproxMap_strictRetraction_mem {φ : (funSpace D E).Element} {y : D.Element}
    {Z : Set β} :
    ((toApproxMap (strictRetraction.toElementMap φ)).toElementMap y).mem Z ↔
      E.mem Z ∧ (Z = E.master ∨ (y ≠ D.bot ∧ ((toApproxMap φ).toElementMap y).mem Z)) := by
  show ((toApproxMap ((curry strictEvalFade).toElementMap φ)).toElementMap y).mem Z ↔ _
  rw [toElementMap_curry_apply]
  show (((fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))).toElementMap
      (pair φ y)).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁, snd_pair,
    evalMap_apply, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

end Strict

end DomainTheory.NeighbourhoodSystems
