module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.finPrefix_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_false
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.bitToNat_true
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.embStr_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Tenum_two
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwFst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwSnd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.pwArg

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

variable {β γ δ : Type*}

/-- **`pointwiseBin h`**: given `f : L → V₀`, `g : L → V₁`, produce the `L`-sequence
`x ↦ h(f x, g x)`. Built by evaluating both factors at the shared argument and applying `h`, then
`curry`-ing. -/
def pointwiseBin {V₀ : NeighborhoodSystem β} {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ}
    (h : ApproximableMap (prod V₀ V₁) V₂) :
    ApproximableMap (prod (funSpace L V₀) (funSpace L V₁)) (funSpace L V₂) :=
  curry (h.comp (paired
    ((evalMap L V₀).comp (paired (pwFst V₀ V₁) (pwArg V₀ V₁)))
    ((evalMap L V₁).comp (paired (pwSnd V₀ V₁) (pwArg V₀ V₁)))))

end DomainTheory.NeighbourhoodSystems.Exercise724
