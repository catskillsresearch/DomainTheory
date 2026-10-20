module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.gf_eq_id

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise317

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap




















/-- **`f` is one-one.** Since `g ∘ f = I_B`, the elementwise map of `f` is injective. -/
theorem f_injective : Function.Injective f.toElementMap := by
  intro x y hxy
  have : (g.comp f).toElementMap x = (g.comp f).toElementMap y := by
    rw [toElementMap_comp, toElementMap_comp, hxy]
  rwa [gf_eq_id, toElementMap_idMap, toElementMap_idMap] at this

end DomainTheory.NeighbourhoodSystems.Exercise317
