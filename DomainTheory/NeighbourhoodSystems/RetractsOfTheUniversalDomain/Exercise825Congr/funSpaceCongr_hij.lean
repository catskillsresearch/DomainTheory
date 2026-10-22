module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.ofIso_comp_ofIso_symm

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem funSpaceCongr_hij (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0.symm) (ofIso e1)).comp (expMap (ofIso e0) (ofIso e1.symm)) =
      idMap (funSpace V₀' V₁') := by
  rw [← expMap_comp, ofIso_comp_ofIso_symm, ofIso_comp_ofIso_symm, expMap_id]

end DomainTheory.NeighbourhoodSystems
