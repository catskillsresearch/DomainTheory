/-ai
The elementwise action of the one-variable map associated with a two-variable approximable map, applied to a pair, equals the two-variable elementwise action.

The bridge lemma relating the two actions, applied to the associated one-variable map, rewrites by the round trip from a two-variable map to its one-variable form, and reversing the resulting equation gives the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- The two-variable elementwise bridge for a general `ApproximableMap₂`, specialized to a pair. -/
theorem toElementMap_ofMap₂_pair {β γ δ : Type*} {V₀ : NeighborhoodSystem β}
    {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ} (f₂ : ApproximableMap₂ V₀ V₁ V₂)
    (p : V₀.Element) (q : V₁.Element) :
    (ofMap₂ f₂).toElementMap (pair p q) = f₂.toElementMap₂ p q := by
  have h := toElementMap₂_toMap₂ (ofMap₂ f₂) p q
  rw [toMap₂_ofMap₂] at h
  exact h.symm

end DomainTheory.NeighbourhoodSystems
