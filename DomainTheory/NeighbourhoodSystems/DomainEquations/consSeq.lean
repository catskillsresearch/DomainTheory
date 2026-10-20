module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The "cons" of a head `a : |𝒟|` and a tail `b : |𝒟^∞|`, as a sequence `⟨a, b₀, b₁, …⟩`. -/
def consSeq (a : V.Element) (b : (iterSys V).Element) : ℕ → V.Element :=
  fun i => Nat.casesOn i a (fun k => component b k)

end Exercise618

end DomainTheory.NeighbourhoodSystems
