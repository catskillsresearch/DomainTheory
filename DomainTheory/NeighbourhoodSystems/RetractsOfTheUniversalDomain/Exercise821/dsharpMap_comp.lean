/-ai
The functorial action of a composite equals the composite of the functorial actions.

Apply uniqueness of the catamorphism to the composite of the two actions, which is strict. On a leaf, the two leaf laws give the leaf embedding of the composite. On a node, the two pairing laws give the pairing of the composite's values. Uniqueness identifies the composite of the actions with the action of the composite.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.gMap_eq_of_satisfies
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_eq

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.pairSharpMap_toElementMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_in
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_pair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_strict
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

/-- **`(f' ∘ f)§ = f'§ ∘ f§`.** Applies `gMap_eq_of_satisfies` to `k := (dsharpMap f').comp
(dsharpMap f)`: both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to
the corresponding equation for `dsharpMap (f'.comp f)` — verbatim
`gMap_selfComp_eq_of_isRetraction`'s proof, generalized away from `f' = f` (so no retraction
hypothesis is needed here). -/
theorem dsharpMap_comp (f : ApproximableMap D₂ D₁) (f' : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₂ (f'.comp f) = (dsharpMap hD₀ hD₁ f').comp (dsharpMap hD₁ hD₂ f) := by
  set g1 : ApproximableMap (Dsharp D₂ hD₂) (Dsharp D₁ hD₁) := dsharpMap hD₁ hD₂ f with hg1_def
  set g2 : ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) := dsharpMap hD₀ hD₁ f' with hg2_def
  symm
  show g2.comp g1 = dsharpMap hD₀ hD₂ (f'.comp f)
  rw [dsharpMap_eq]
  apply gMap_eq_of_satisfies
  · exact isStrict_comp (by rw [hg2_def, dsharpMap_eq]; exact gMap_strict hD₁)
      (by rw [hg1_def, dsharpMap_eq]; exact gMap_strict hD₂)
  · intro x
    have e1 : g1.toElementMap (inSharp D₂ hD₂ x) = inSharp D₁ hD₁ (f.toElementMap x) := by
      rw [hg1_def, dsharpMap_eq, gMap_in hD₂ x, toElementMap_comp, inSharpMap_toElementMap]
    have e2 : g2.toElementMap (inSharp D₁ hD₁ (f.toElementMap x))
        = inSharp D₀ hD₀ (f'.toElementMap (f.toElementMap x)) := by
      rw [hg2_def, dsharpMap_eq, gMap_in hD₁ (f.toElementMap x), toElementMap_comp,
        inSharpMap_toElementMap]
    calc (g2.comp g1).toElementMap (inSharp D₂ hD₂ x)
        = g2.toElementMap (g1.toElementMap (inSharp D₂ hD₂ x)) := toElementMap_comp _ _ _
      _ = g2.toElementMap (inSharp D₁ hD₁ (f.toElementMap x)) := by rw [e1]
      _ = inSharp D₀ hD₀ (f'.toElementMap (f.toElementMap x)) := e2
      _ = ((inSharpMap hD₀).comp (f'.comp f)).toElementMap x := by
          rw [toElementMap_comp, toElementMap_comp, inSharpMap_toElementMap]
  · intro y z
    have e1 : g1.toElementMap (pairSharp D₂ hD₂ y z)
        = pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z) := by
      rw [hg1_def, dsharpMap_eq, gMap_pair hD₂ y z, pairSharpMap_toElementMap]
    have e2 : g2.toElementMap (pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z))
        = pairSharp D₀ hD₀ (g2.toElementMap (g1.toElementMap y))
          (g2.toElementMap (g1.toElementMap z)) := by
      rw [hg2_def, dsharpMap_eq, gMap_pair hD₁ (g1.toElementMap y) (g1.toElementMap z),
        pairSharpMap_toElementMap]
    calc (g2.comp g1).toElementMap (pairSharp D₂ hD₂ y z)
        = g2.toElementMap (g1.toElementMap (pairSharp D₂ hD₂ y z)) := toElementMap_comp _ _ _
      _ = g2.toElementMap (pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z)) := by
          rw [e1]
      _ = pairSharp D₀ hD₀ (g2.toElementMap (g1.toElementMap y))
          (g2.toElementMap (g1.toElementMap z)) := e2
      _ = (pairSharpMap hD₀).toElementMap
          (pair (g2.toElementMap (g1.toElementMap y)) (g2.toElementMap (g1.toElementMap z))) :=
        (pairSharpMap_toElementMap hD₀ _ _).symm
      _ = (pairSharpMap hD₀).toElementMap
          (pair ((g2.comp g1).toElementMap y) ((g2.comp g1).toElementMap z)) := by
        rw [toElementMap_comp, toElementMap_comp]

end DsharpFunctor

end DomainTheory.NeighbourhoodSystems
