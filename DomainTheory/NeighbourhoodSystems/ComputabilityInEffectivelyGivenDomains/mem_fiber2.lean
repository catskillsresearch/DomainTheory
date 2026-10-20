module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

@[simp] theorem mem_fiber2 {S : Set (ℕ × (ℕ × α))} {i j : ℕ} {a : α} :
    a ∈ fiber2 S i j ↔ (i, (j, a)) ∈ S := Iff.rfl

end Exercise718

end DomainTheory.NeighbourhoodSystems
