/-ai
Scott's guard for the discriminator says that a sum neighborhood W may be sent to a truth neighborhood C in exactly three ways: W is a left copy and C is the master or the zero token, W is a right copy and C is the master or the one token, or W is the sum master and C is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- Scott's guard for `which`: the truth output is `true` (`{0}`/`Δ`) on a left copy `0X`, `false`
(`{1}`/`Δ`) on a right copy `1Y`, and `⊥` (`Δ`) on the basepoint master. -/
def whichGuard (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (W : Set (Option (α ⊕ β))) (C : Set Example12.Token) : Prop :=
  ((∃ X, V₀.mem X ∧ W = inj₀ X) ∧ (C = Example12.master ∨ C = Example12.zero)) ∨
  ((∃ Y, V₁.mem Y ∧ W = inj₁ Y) ∧ (C = Example12.master ∨ C = Example12.one)) ∨
  (W = sumMaster V₀ V₁ ∧ C = Example12.master)

end DomainTheory.NeighbourhoodSystems.Exercise326
