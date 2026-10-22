module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.GRel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Related outputs are `E`-neighbourhoods. -/
theorem gRel_cod {W Z} (h : GRel u v W Z) : E.mem Z := by
  induction h with
  | gamma hZ => exact hZ ▸ E.master_mem
  | leaf hrel => exact u.rel_cod hrel
  | node _ _ hvrel _ _ => exact v.rel_cod hvrel

end Exercise717

end DomainTheory.NeighbourhoodSystems
