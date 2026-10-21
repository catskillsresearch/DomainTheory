/-ai
The forward reindexing map relates two neighbourhoods exactly when both are neighbourhoods of the corresponding iterated systems and every fiber at a paired index is contained in the corresponding double fiber.

The two sides are the same by the definition of the relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

@[simp] theorem Fmap_rel {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    (Fmap V).rel W S ↔ (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
      ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := Iff.rfl

end Exercise718

end DomainTheory.NeighbourhoodSystems
