/-ai
If n₀ is the least zero of f at the numeral m, in the sense that f at the numerals n₀ and m is the numeral 0 and f at each smaller numeral and m is a positive numeral, then the minimization at the numeral m is the numeral n₀.

The numbered name theorem_56 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem56.muMap_eq_least

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem56

set_option linter.unusedVariables false

theorem theorem_56 : ∀
  (f :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum Nat Nat) Nat
      (@DomainTheory.NeighbourhoodSystems.prod Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.N)
      DomainTheory.NeighbourhoodSystems.Example43.N)
  {m n₀ : Nat},
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum Nat Nat) Nat
        (@DomainTheory.NeighbourhoodSystems.prod Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
          DomainTheory.NeighbourhoodSystems.Example43.N)
        DomainTheory.NeighbourhoodSystems.Example43.N f
        (@DomainTheory.NeighbourhoodSystems.pair Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
          DomainTheory.NeighbourhoodSystems.Example43.N (DomainTheory.NeighbourhoodSystems.Example43.natElem n₀)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem m)))
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    (∀ (i : Nat),
        @LT.lt Nat instLTNat i n₀ →
          ∃ (j : Nat),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum Nat Nat) Nat
                (@DomainTheory.NeighbourhoodSystems.prod Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                DomainTheory.NeighbourhoodSystems.Example43.N f
                (@DomainTheory.NeighbourhoodSystems.pair Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
                  DomainTheory.NeighbourhoodSystems.Example43.N (DomainTheory.NeighbourhoodSystems.Example43.natElem i)
                  (DomainTheory.NeighbourhoodSystems.Example43.natElem m)))
              (DomainTheory.NeighbourhoodSystems.Example43.natElem
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) j
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
          DomainTheory.NeighbourhoodSystems.Example43.N)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
          DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
          (DomainTheory.NeighbourhoodSystems.Theorem56.muMap f) (DomainTheory.NeighbourhoodSystems.Example43.natElem m))
        (DomainTheory.NeighbourhoodSystems.Example43.natElem n₀) :=
  DomainTheory.NeighbourhoodSystems.Theorem56.muMap_eq_least

end DomainTheory.NeighbourhoodSystems.Theorem56
