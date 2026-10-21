/-ai
The universal strict map is strict: it sends the bottom element to the bottom element.

A relation out of the master neighbourhood forces the target to be the master neighbourhood, by inversion at the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}















/-- **`g` is strict** (`g(⊥) = ⊥`): Scott's "the unique *strict* mapping". -/
theorem gMap_strict (hD : ∀ X, D.mem X → X.Nonempty) :
    IsStrict (gMap u v hD) := fun _ h => gRel_gamma_inv hD h

end Exercise717
end DomainTheory.NeighbourhoodSystems
