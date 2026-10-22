module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmapComb
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PDmem_down
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)


end NeighborhoodSystem

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}


@[simp] theorem PFmapComb_rel {Φ : Set (ApproximableMap V W)}
    {Ψ : Set (ApproximableMap V.PowerDomain W.PowerDomain)} :
    (PFmapComb V W).rel Φ Ψ ↔
      (funSpace V W).mem Φ ∧ (funSpace V.PowerDomain W.PowerDomain).mem Ψ ∧
        ∀ f ∈ Φ, PFmap f ∈ Ψ := Iff.rfl
end DomainTheory.NeighbourhoodSystems
