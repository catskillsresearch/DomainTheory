module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.projectionPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.projPairSubdomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*}

/-- Scott's Proposition 6.12: a subdomain yields injection and projection with the two laws. -/
theorem proposition_612 :
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E),
      h.inj.comp h.proj ≤ idMap E) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E),
      h.proj.comp h.inj = idMap D) :=
  ⟨@inj_comp_proj_le, @proj_comp_inj⟩

theorem Subsystem.trianglelefteq {D E : NeighborhoodSystem α} (h : D ◁ E) : D ⊴ E :=
  ⟨D, h, Isomorphic.refl D⟩

end DomainTheory.NeighbourhoodSystems
