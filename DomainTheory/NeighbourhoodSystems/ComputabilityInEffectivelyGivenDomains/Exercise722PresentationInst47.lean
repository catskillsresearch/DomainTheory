module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_char_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Scott's consistency relation (Definition 7.1 (ii)) on the `SsysX` indices is decidable via
`ssysConsistentB` (choice-free on the `Bool` side; see axiom audit of `decideNonemptyB_iff`). -/
instance decidableSsysCons (n m : ℕ) :
    Decidable (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  decidable_of_iff (ssysConsistentB n m = true) (ssys_cons_char_iff n m)

end Exercise722

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_presentation_inst47 : ∀ (n m : Nat),
  Iff (@Eq Bool (DomainTheory.NeighbourhoodSystems.Exercise722.ssysConsistentB n m) Bool.true)
    (∃ (k : Nat),
      @LE.le (Set (List Bool)) (@Set.instLE (List Bool)) (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX k)
        (@Inter.inter (Set (List Bool)) (@Set.instInter (List Bool))
          (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX n)
          (DomainTheory.NeighbourhoodSystems.Exercise722.SsysX m))) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.ssys_cons_char_iff

end DomainTheory.NeighbourhoodSystems.Exercise722
