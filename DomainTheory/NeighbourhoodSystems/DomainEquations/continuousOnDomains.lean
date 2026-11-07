module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition_6_10
public import DomainTheory.NeighbourhoodSystems.DomainEquations.endofunctor
public import DomainTheory.NeighbourhoodSystems.DomainEquations.initialAlgebra
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.DomainObj

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w

structure MonotoneAt (T : Endofunctor DomainObj.{w}) {α : Type w}
    {D E : NeighborhoodSystem α} (h : D ◁ E) : Prop where
  carrier_eq : (T.obj ⟨α, E⟩).carrier = (T.obj ⟨α, D⟩).carrier
  sub : (T.obj ⟨α, D⟩).sys ◁
    (carrier_eq ▸ (T.obj ⟨α, E⟩).sys : NeighborhoodSystem (T.obj ⟨α, D⟩).carrier)
  inj_heq : HEq (T.map (X := ⟨α, D⟩) (Y := ⟨α, E⟩) h.inj) sub.inj
  proj_heq : HEq (T.map (X := ⟨α, E⟩) (Y := ⟨α, D⟩) h.proj) sub.proj

def MonotoneOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∀ {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E), MonotoneAt T h

def targetFam (T : Endofunctor DomainObj.{w}) (hmono : MonotoneOnDomains T)
    {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    Set (Set (T.obj ⟨α, E⟩).carrier) :=
  {Y | (T.obj ⟨α, D⟩).sys.mem ((hmono h).carrier_eq ▸ Y)}

def ContinuousOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∃ hmono : MonotoneOnDomains T,
    ∀ {α : Type w} {E : NeighborhoodSystem α}
      (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
      (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
      {U : NeighborhoodSystem α} (hUE : U ◁ E)
      (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
      targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD)

theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩

theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_iUnion, exists_prop]
  exact hU Y

end DomainTheory.NeighbourhoodSystems
