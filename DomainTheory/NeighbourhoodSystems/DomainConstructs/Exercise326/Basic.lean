module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.TD
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.one_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Tmem_eq_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.Tmem_eq_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_components

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}


variable (V : NeighborhoodSystem α)


@[simp] theorem cond_rel {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} :
    (cond V).rel W Z ↔ (prod TD (prod V V)).mem W ∧ V.mem Z ∧ condGuard V W Z := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise326
