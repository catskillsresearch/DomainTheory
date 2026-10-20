module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718









namespace IsComputableSplit

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

/-- The split's first output is a genuine `W`-neighbourhood whenever it is non-empty (immediate
from `posIdx_spec` and `Q.mem_X`). Unlike the structure's original (unconditional) design, this is
now conditional on `(split …).1 ≠ ∅` — see `posIdx_spec`'s docstring. -/
theorem posIdx_mem (h : IsComputableSplit P Q split) (n m k : ℕ)
    (hne : (split (P.X n) (Q.X m) (P.X k)).1 ≠ ∅) :
    W.mem (split (P.X n) (Q.X m) (P.X k)).1 := by
  rw [h.posIdx_spec n m k hne]; exact Q.mem_X _

end IsComputableSplit
end DomainTheory.NeighbourhoodSystems
