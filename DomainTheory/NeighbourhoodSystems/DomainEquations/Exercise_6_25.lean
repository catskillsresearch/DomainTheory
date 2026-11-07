module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.projPairLaws

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair

theorem example_625 :
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) (x : D.Element) (y : E.Element),
        P.inj.toElementMap x ≤ y ↔ x ≤ P.proj.toElementMap y) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) {S : Set D.Element},
        D.Bounded S → E.Bounded (P.inj.toElementMap '' S)) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) (x : D.Element),
        P.inj.toElementMap x = E.sInf (P.upperSet x) (P.upperSet_nonempty x)) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S),
        P.inj.toElementMap (D.sSup S hS) = E.sSup (P.inj.toElementMap '' S) (P.inj_bounded hS)) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) (y : E.Element),
        ∀ a ∈ P.lowerSet y, ∀ b ∈ P.lowerSet y, ∃ c ∈ P.lowerSet y, a ≤ c ∧ b ≤ c) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) (y : E.Element),
        P.proj.toElementMap y = D.sSup (P.lowerSet y) (P.lowerSet_bounded y)) ∧
    (∀ {α : Type*} {D E : NeighborhoodSystem α} (P : ProjectionPair D E) (x : D.Element),
        (P.upperSet x).Nonempty) :=
  ⟨@galois, ⟨@inj_bounded, ⟨@inj_eq_sInf, ⟨@inj_sSup, ⟨@lowerSet_directed, ⟨@proj_eq_sSup, @upperSet_nonempty⟩⟩⟩⟩⟩⟩

end DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair
