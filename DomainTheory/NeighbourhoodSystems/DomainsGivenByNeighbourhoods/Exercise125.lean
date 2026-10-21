/-ai
Every element of the final-segment system approximates the filter of all neighbourhoods.

The numbered name example_125 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.FinalSegment

set_option linter.unusedVariables false

theorem example_125.{u_1} : And
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Δ
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1))
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    (∀ (a : Δ),
        ∃ (b : Δ),
          @LT.lt Δ
            (@Preorder.toLT Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst))))))
            a b) →
      ∀ (a : Δ),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1))
          (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
            (@Set.Ici Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst)))))
              a)
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.Ici_mem Δ inst inst_1 a))) :=
  @And.intro
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Δ
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1))
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    (∀ (a : Δ),
        ∃ (b : Δ),
          @LT.lt Δ
            (@Preorder.toLT Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst))))))
            a b) →
      ∀ (a : Δ),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1))
          (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
            (@Set.Ici Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst)))))
              a)
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.Ici_mem Δ inst inst_1 a)))
  @DomainTheory.NeighbourhoodSystems.FinalSegment.topElement_isTotal
  @DomainTheory.NeighbourhoodSystems.FinalSegment.topElement_not_principal_of_noMax

end DomainTheory.NeighbourhoodSystems.FinalSegment
