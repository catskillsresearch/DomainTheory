module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.eq_computable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

variable {P₀ P₁}

variable (P₀ P₁)

theorem proper₁_dec : RecDecidable (fun n => P₁.X n ≠ V₁.master) := by
  have heq : RecDecidable (fun n => P₁.X n = V₁.master) := by
    refine RecDecidable.of_iff (fun n => ?_)
      (P₁.eq_computable.comp (primrec_id.pair (Nat.Primrec.const P₁.masterIdx)))
    simp only [unpair_pair_fst, unpair_pair_snd, P₁.masterIdx_spec, id_eq]
  exact heq.not

end Smash

end DomainTheory.NeighbourhoodSystems
