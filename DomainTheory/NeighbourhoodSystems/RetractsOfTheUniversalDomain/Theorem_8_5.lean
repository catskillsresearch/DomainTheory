module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.fixedNbhd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Theorem 8.5: a projection is finitary precisely when its action on
elements is given by the neighbourhood formula with a self-related witness. -/
theorem theorem_85 :
    (∀ {α : Type*} {E : NeighborhoodSystem α} {a : ApproximableMap E E},
      FinitaryProjection a →
        ∀ (x : E.Element) {Y : Set α},
          (a.toElementMap x).mem Y ↔
            E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) ∧
    (∀ {α : Type*} {E : NeighborhoodSystem α} (a : ApproximableMap E E),
      FinitaryProjection a ↔
        ∀ (x : E.Element) {Y : Set α},
          (a.toElementMap x).mem Y ↔
            E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) ∧
    (∀ {α : Type*} {E : NeighborhoodSystem α} (a : ApproximableMap E E),
      (∀ (x : E.Element) {Y : Set α},
        (a.toElementMap x).mem Y ↔
          E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) →
      FinitaryProjection a) :=
  ⟨@formula_of_isFinitaryProjection, @finitaryProjection_iff_formula,
    @isFinitaryProjection_of_formula⟩

end DomainTheory.NeighbourhoodSystems
