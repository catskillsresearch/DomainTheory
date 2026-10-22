module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C_dir
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.graphEquiv

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.reprIso
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 3.27.** The function space `|𝒟₀ → 𝒟₁|` is (order-)isomorphic to the domain produced by
the *abstract* representation theorem (Exercise 2.22) applied to the family `C` of graphs of
approximable maps. This re-proves that approximable mappings form a domain without appealing to the
explicit step-set neighbourhood system of Definition 3.8 — composing Exercise 2.22's `reprIso` with
the graph isomorphism (`graphEquiv`) and Theorem 3.10 (`funSpaceEquiv`). -/
noncomputable def funSpaceReprIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (Exercise222.reprSystem (C V₀ V₁) C_inter C_nonempty).Element ≃o (funSpace V₀ V₁).Element :=
  (Exercise222.reprIso (C V₀ V₁) C_inter C_nonempty C_dir).trans
    ((graphEquiv V₀ V₁).symm.trans (funSpaceEquiv V₀ V₁).symm)

end DomainTheory.NeighbourhoodSystems.Exercise327
