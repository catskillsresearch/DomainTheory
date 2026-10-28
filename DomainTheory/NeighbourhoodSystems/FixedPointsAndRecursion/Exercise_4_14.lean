module

public import Mathlib.Order.BourbakiWitt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise414
end DomainTheory.NeighbourhoodSystems.Exercise414

section
namespace DomainTheory.NeighbourhoodSystems.Exercise414
section
variable {A : Type*}

def gfpSet (f : Set A → Set A) : Set A := {a | ∃ x : Set A, x ⊆ f x ∧ a ∈ x}

def lfpSet (f : Set A → Set A) : Set A := {a | ∀ x : Set A, f x ⊆ x → a ∈ x}

theorem lfpSet_subset (f : Set A → Set A) {x : Set A} (hx : f x ⊆ x) : lfpSet f ⊆ x :=
  fun _ ha => ha x hx

theorem f_subset_lfpSet (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) ⊆ lfpSet f := by
  intro a ha x hx
  exact hx (hf (lfpSet_subset f hx) ha)

theorem lfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) = lfpSet f := by
  have hsub : f (lfpSet f) ⊆ lfpSet f := f_subset_lfpSet f hf
  have hsup : lfpSet f ⊆ f (lfpSet f) := lfpSet_subset f (hf hsub)
  exact Set.Subset.antisymm hsub hsup

theorem lfpSet_least (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    lfpSet f ⊆ y := lfpSet_subset f (le_of_eq hy)

theorem subset_gfpSet (f : Set A → Set A) {x : Set A} (hx : x ⊆ f x) : x ⊆ gfpSet f :=
  fun _ ha => ⟨x, hx, ha⟩

theorem gfpSet_greatest (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    y ⊆ gfpSet f := subset_gfpSet f (le_of_eq hy.symm)

theorem gfpSet_subset_f (f : Set A → Set A) (hf : Monotone f) :
    gfpSet f ⊆ f (gfpSet f) := by
  rintro a ⟨x, hx, hax⟩
  exact hf (subset_gfpSet f hx) (hx hax)

theorem gfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (gfpSet f) = gfpSet f := by
  have hsub : gfpSet f ⊆ f (gfpSet f) := gfpSet_subset_f f hf
  have hsup : f (gfpSet f) ⊆ gfpSet f := subset_gfpSet f (hf hsub)
  exact Set.Subset.antisymm hsup hsub

end

section
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
end

end DomainTheory.NeighbourhoodSystems.Exercise414
end
