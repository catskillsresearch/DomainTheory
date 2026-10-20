module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition712.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}



/-- A subsystem of an unconditionally ∩-closed system is itself unconditionally ∩-closed: the
`◁`-clause `inter_closed` routes the intersection through `E`. -/
theorem subsystem_inter_closed {D E : NeighborhoodSystem γ} (h : D ◁ E)
    (hE : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y))
    {X Y : Set γ} (hX : D.mem X) (hY : D.mem Y) : D.mem (X ∩ Y) :=
  h.inter_closed hX hY (hE (h.sub hX) (h.sub hY))

end Counterexample712C
end DomainTheory.NeighbourhoodSystems
