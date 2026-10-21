/-ai
The action of prepending a word on a domain element is the product of the embedding of that word with the element.

A neighbourhood witnessing the action of the approximable map, together with the singleton of the word, witnesses the product. Conversely, any neighbourhood of the embedding contains the word, so monotonicity of concatenation shrinks the left factor of the product witness to that singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap



























/-- `(prependMap σ).toElementMap y = σ · y`: the approximable-map action agrees with Scott's
multiplication `mulElem`, using `{σ} ⊆ X` (any valid witness `X` for `emb σ` contains `σ`) to
tighten the witness set to `{σ}` without loss. -/
theorem prependMap_toElementMap (σ : List Bool) (y : Ssys.Element) :
    (prependMap σ).toElementMap y = mulElem (emb σ) y := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hY, hInSY, hInSZ, hsub⟩
    exact ⟨hInSZ, {σ}, ⟨InS.singleton σ, rfl⟩, Y, hY, hsub⟩
  · rintro ⟨hInSZ, X, ⟨_, hσX⟩, Y, hY, hsub⟩
    refine ⟨Y, hY, y.sub hY, hInSZ, ?_⟩
    exact (concat_mono (Set.singleton_subset_iff.mpr hσX) (Set.Subset.refl _)).trans hsub

end Exercise722
end DomainTheory.NeighbourhoodSystems
