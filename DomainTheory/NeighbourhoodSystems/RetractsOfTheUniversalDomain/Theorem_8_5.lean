module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_3

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

theorem finitaryProjection_iff_formula (a : ApproximableMap E E) :
    FinitaryProjection a ↔ ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X :=
  ⟨fun h => formula_of_isFinitaryProjection h, fun hii => isFinitaryProjection_of_formula a hii⟩
end

open NeighborhoodSystem ApproximableMap

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
