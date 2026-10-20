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

























/-- The embedding is **injective**: distinct words give distinct elements of `|S|`. (If
`emb σ = emb τ` then `emb τ` contains `{σ}`, forcing `τ = σ`.) So `Σ` genuinely *embeds* into `|S|`. -/
theorem emb_injective : Function.Injective emb := by
  intro σ τ h
  have hmem : (emb τ).mem {σ} := h ▸ (⟨InS.singleton σ, rfl⟩ : (emb σ).mem {σ})
  exact (Set.mem_singleton_iff.mp hmem.2).symm

end Exercise722
end DomainTheory.NeighbourhoodSystems
