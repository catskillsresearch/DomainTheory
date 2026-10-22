module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.U_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.iPlus
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89.jPlus

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

/-- **`a + b : 𝒰 → 𝒰`** (Definition 8.9): `cond ∘ ⟨which, i₊∘in₀∘a∘out₀, i₊∘in₁∘b∘out₁⟩ ∘ j₊`. -/
noncomputable def sumComb (a b : ApproximableMap U U) : ApproximableMap U U :=
  (cond U).comp
    ((paired (whichMap U U U_mem_nonempty U_mem_nonempty)
        (paired (iPlus.comp ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                  (a.comp (outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)))))
                (iPlus.comp ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                  (b.comp (outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty))))))).comp
      jPlus)

end DomainTheory.NeighbourhoodSystems
