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
