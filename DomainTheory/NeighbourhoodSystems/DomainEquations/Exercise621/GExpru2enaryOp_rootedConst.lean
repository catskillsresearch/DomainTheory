/-ai
An n-ary fold preserves the rooted-constant condition whenever the binary operation does. Each of separated sum, separated product, coalesced sum, and smash product preserves it definitionally.

The proof inducts on the list. An empty tail returns the hypothesis on the head. A cons cell rewrites the fold and the rootedness equivalence of the operation, then pairs the head hypothesis with the inductive result on the tail, using that the head belongs to the cons list and that every remaining entry belongs to the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}


variable {C₀ C₁ : ScottSys}


/-- The `Λ ∈ tok` side-condition is preserved by any n-ary fold whose binary operation preserves it
(all four of `+`, `×`, `⊕`, `⊗` do, definitionally). -/
theorem GExpr.naryOp_rootedConst {op : GExpr → GExpr → GExpr}
    (hop : ∀ x y, (op x y).RootedConst ↔ x.RootedConst ∧ y.RootedConst) :
    ∀ (a : GExpr) (l : List GExpr), a.RootedConst → (∀ b ∈ l, b.RootedConst) →
      (GExpr.naryOp op a l).RootedConst
  | a, [], ha, _ => ha
  | a, b :: l, ha, hl => by
      rw [GExpr.naryOp, hop]
      exact ⟨ha, GExpr.naryOp_rootedConst hop b l (hl b (List.mem_cons_self ..))
        (fun c hc => hl c (List.mem_cons_of_mem _ hc))⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
