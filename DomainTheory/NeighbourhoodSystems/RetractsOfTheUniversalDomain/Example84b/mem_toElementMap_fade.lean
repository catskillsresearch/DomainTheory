/-ai
For an arbitrary neighbourhood system G, a neighbourhood Z belongs to fade applied to the pair of t and w if and only if Z is a G-neighbourhood and either Z is the master or t contains {0} and w contains Z.

Unfold fade as the one-variable form of fade₂, apply the pair bridge, and use the closed form of the two-variable action.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- The closed form of `fade`'s elementwise action, generalized (via `mem_toElementMap₂_fade`) from
Example 8.4(a)'s ambient `D` to an arbitrary neighbourhood system `G`. -/
theorem mem_toElementMap_fade {γ : Type*} {G : NeighborhoodSystem γ} (t : O.Element) (w : G.Element)
    {Z : Set γ} :
    ((fade (D := G)).toElementMap (pair t w)).mem Z ↔
      G.mem Z ∧ (Z = G.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ w.mem Z)) := by
  rw [show (fade (D := G)) = ofMap₂ (fade₂ (D := G)) from rfl, toElementMap_ofMap₂_pair,
    mem_toElementMap₂_fade]

end DomainTheory.NeighbourhoodSystems
