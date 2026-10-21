/-ai
Every n-ary construct has a solution Γ = tok(T({Γ})), so the singleton system on Γ is a subsystem of T applied to that singleton and Theorem 6.14 applies. The argument is given for the n-ary separated sum, and the same argument applies to the n-ary separated product, coalesced sum, and smash product.

The general singleton-subsystem solution applies to this fold. Rootedness of the fold is the preservation lemma for n-ary folds, using that rootedness of a separated sum is definitionally the conjunction of rootedness of its two arguments.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpru2enaryOp_rootedConst

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


/-- **Every n-ary construct has a solution `Γ = tok(T({Γ}))`** (so `{Γ} ◁ T({Γ})` and 6.14 applies),
illustrated for the n-ary separated sum; identical for `naryProd`/`naryOplus`/`naryOtimes`. -/
theorem narySum_singleton_subsystem (a : GExpr) (l : List GExpr)
    (ha : a.RootedConst) (hl : ∀ b ∈ l, b.RootedConst) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((GExpr.narySum a l).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem _ (GExpr.naryOp_rootedConst (fun _ _ => Iff.rfl) a l ha hl)

end Exercise619
end DomainTheory.NeighbourhoodSystems
