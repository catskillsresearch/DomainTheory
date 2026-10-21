/-ai
It is recursively decidable whether an enumerated left neighbourhood is distinct from the left master.

Equality with the master is the equality predicate on enumerated neighbourhoods, evaluated at the code and the constant master index. Properness is the negation of that predicate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.eq_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

/-- The properness predicate `Xₙ ≠ Δ₀` is recursively decidable (negation of `eq_computable`
against the master index). -/
theorem proper₀_dec : RecDecidable (fun n => P₀.X n ≠ V₀.master) := by
  have heq : RecDecidable (fun n => P₀.X n = V₀.master) := by
    refine RecDecidable.of_iff (fun n => ?_)
      (P₀.eq_computable.comp (primrec_id.pair (Nat.Primrec.const P₀.masterIdx)))
    simp only [unpair_pair_fst, unpair_pair_snd, P₀.masterIdx_spec, id_eq]
  exact heq.not

end Smash

end DomainTheory.NeighbourhoodSystems
