module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.sumEnum_one

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

section Sum

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

variable {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}

/-- Equality of two enumerated `𝒟₀`-neighbourhoods is recursively decidable (antisymmetry of `⊆`,
decided by `incl_computable`). -/
theorem recDec_setEq₀ {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    RecDecidable (fun u => P₀.X (f u) = P₀.X (g u)) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  refine RecDecidable.of_iff (fun u => ?_) ((hincl.comp (hf.pair hg)).and (hincl.comp (hg.pair hf)))
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => ⟨h.subset, h.symm.subset⟩, fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2⟩

end Sum

end DomainTheory.NeighbourhoodSystems
