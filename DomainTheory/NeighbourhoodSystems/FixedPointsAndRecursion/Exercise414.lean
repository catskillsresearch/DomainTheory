module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.gfpSet_greatest
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.gfpSet_isFixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise414

set_option linter.unusedVariables false

theorem example_414.{u_1} : And
  (∀ {A : Type u_1} (f : Set A → Set A) {y : Set A},
    @Eq (Set A) (f y) y → @LE.le (Set A) (@Set.instLE A) y (@DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet A f))
  (∀ {A : Type u_1} (f : Set A → Set A),
    @Monotone (Set A) (Set A)
        (@PartialOrder.toPreorder (Set A)
          (@SemilatticeInf.toPartialOrder (Set A)
            (@Lattice.toSemilatticeInf (Set A) (@DistribLattice.toLattice (Set A) (@Set.instDistribLattice A)))))
        (@PartialOrder.toPreorder (Set A)
          (@SemilatticeInf.toPartialOrder (Set A)
            (@Lattice.toSemilatticeInf (Set A) (@DistribLattice.toLattice (Set A) (@Set.instDistribLattice A)))))
        f →
      @Eq (Set A) (f (@DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet A f))
        (@DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet A f)) :=
  @And.intro
  (∀ {A : Type u_1} (f : Set A → Set A) {y : Set A},
    @Eq (Set A) (f y) y → @LE.le (Set A) (@Set.instLE A) y (@DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet A f))
  (∀ {A : Type u_1} (f : Set A → Set A),
    @Monotone (Set A) (Set A)
        (@PartialOrder.toPreorder (Set A)
          (@SemilatticeInf.toPartialOrder (Set A)
            (@Lattice.toSemilatticeInf (Set A) (@DistribLattice.toLattice (Set A) (@Set.instDistribLattice A)))))
        (@PartialOrder.toPreorder (Set A)
          (@SemilatticeInf.toPartialOrder (Set A)
            (@Lattice.toSemilatticeInf (Set A) (@DistribLattice.toLattice (Set A) (@Set.instDistribLattice A)))))
        f →
      @Eq (Set A) (f (@DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet A f))
        (@DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet A f))
  @DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet_greatest
  @DomainTheory.NeighbourhoodSystems.Exercise414.gfpSet_isFixed

end DomainTheory.NeighbourhoodSystems.Exercise414
