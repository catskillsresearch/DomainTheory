/-ai
Every partial recursive function of finitely many natural numbers has a very strict λ-definition: an approximable map from the universal argument domain to N that returns the function's value on total arguments, returns bottom where the function is undefined, and returns bottom on any argument-like input with bottom among its first coordinates.

The numbered name theorem_56_full is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56Full.partrec_lamDef

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56Full

set_option linter.unusedVariables false

theorem theorem_56_full : ∀ {n : Nat} {f : PFun (List.Vector Nat n) Nat},
  @Nat.Partrec' n f →
    ∃ (φ :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat Nat) Nat
        DomainTheory.NeighbourhoodSystems.Theorem56Full.𝒩 DomainTheory.NeighbourhoodSystems.Example43.N),
      @DomainTheory.NeighbourhoodSystems.Theorem56Full.LamDef n φ f :=
  @DomainTheory.NeighbourhoodSystems.Theorem56Full.partrec_lamDef

end DomainTheory.NeighbourhoodSystems.Theorem56Full
