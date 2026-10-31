module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap

@[expose] public section

namespace DomainTheory.ContinuousLattice

variable {D : Type*} [CompleteLattice D]

theorem proposition_3_14 (_hD : ContinuousLattice D) :
    ∃ Fix : ScottMap (ScottMap D D) D,
      (∀ f : ScottMap D D, (f : D → D) (Fix f) = Fix f)
        ∧ (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → (Fix f : D) ≤ x)
        ∧ (∀ g : ScottMap D D → D,
            (∀ f : ScottMap D D, (f : D → D) (g f) = g f) →
            (∀ (f : ScottMap D D) (x : D), (f : D → D) x ≤ x → g f ≤ x) →
            ∀ f : ScottMap D D, g f = Fix f) :=
  ⟨ScottMap.fixMap, fun f => ScottMap.fix_eq f,
    fun _ _ h => ScottMap.fix_le h,
    fun _ hfix hleast f => ScottMap.fix_unique (hfix f) (fun x hx => hleast f x hx)⟩

end DomainTheory.ContinuousLattice
