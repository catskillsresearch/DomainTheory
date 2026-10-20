module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.primrec_inclShuffle

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

/-- The inclusion relation is decidable: `Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`. -/
theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

end ScottPresentation

end DomainTheory.NeighbourhoodSystems
