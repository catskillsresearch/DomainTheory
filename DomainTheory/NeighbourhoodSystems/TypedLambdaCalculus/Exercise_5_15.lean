module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.langStar

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open LangStar Pointwise

/-- Scott's Exercise 5.15: Arden's lemma for singleton generators, and Park's least
solution of the two-variable language equations. -/
theorem example_515 :
    (∀ (e e' : FreeMonoid Bool),
      lfpSet (fun w => ({e} : Set (FreeMonoid Bool)) * w ∪ {e'}) =
        star ({e} : Set (FreeMonoid Bool)) * {e'}) ∧
    (∀ {S : Type*} [Monoid S] (a b c d : Set S),
      parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c ∧
        parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d) ∧
    (∀ {S : Type*} [Monoid S] (a b c d : Set S) {x y : Set S},
      x = a * x ∪ b * y ∪ c → y = b * x ∪ a * y ∪ d →
        parkX a b c d ⊆ x ∧ parkY a b c d ⊆ y) :=
  ⟨part1_freeMonoid, @park_solves, fun a b c d _ _ hx hy => park_least a b c d hx hy⟩

end DomainTheory.NeighbourhoodSystems
