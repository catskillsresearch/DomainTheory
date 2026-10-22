module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.Basic

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127.le_sSup
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem le_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ F) : f ≤ sSupMaps F hF := by
  intro X Y hrel
  have hX : V₀.mem X := f.rel_dom hrel
  have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
  exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hF hX) ⟨f, hf, rfl⟩) Y hmem⟩

end DomainTheory.NeighbourhoodSystems
