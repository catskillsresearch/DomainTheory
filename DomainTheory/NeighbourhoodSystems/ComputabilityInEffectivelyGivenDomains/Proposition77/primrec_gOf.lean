module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.gOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.primrec_rtbl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- `gOf step` is primitive recursive when `step` is. -/
theorem primrec_gOf {step : ℕ → ℕ} (hstep : Nat.Primrec step) : Nat.Primrec (gOf step) :=
  (hstep.comp (primrec_id.pair (primrec_rtbl hstep))).of_eq fun _ => rfl

end Proposition77

end DomainTheory.NeighbourhoodSystems
