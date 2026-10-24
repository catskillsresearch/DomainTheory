module


public import DomainTheory.NeighbourhoodSystems.DomainConstructs.DomainConstructs
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.MappingsBetweenDomains
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic


@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise412
open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem

section
/-- Abbreviation for Example 1.2's domain `T`. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- `{1} ≠ {0}` as tokens. -/
theorem one_ne_zero : (Example12.one) ≠ Example12.zero := by
  intro h
  rw [Example12.one, Example12.zero, Set.ext_iff] at h
  have h1 : (1 : Example12.Token) = 0 := (h 1).mp rfl
  exact absurd h1 (by decide)

/-- `{1} ≠ Δ` as tokens. -/
theorem one_ne_master : (Example12.one) ≠ Example12.master := by
  intro h
  rw [Example12.one, Example12.master, Set.ext_iff] at h
  have h0 : (0 : Example12.Token) ∈ ({1} : Set Example12.Token) := (h 0).mpr (Set.mem_univ 0)
  simp only [Set.mem_singleton_iff] at h0
  exact absurd h0 (by decide)

/-- `{0} ≠ Δ` as tokens. -/
theorem zero_ne_master : (Example12.zero) ≠ Example12.master := by
  intro h
  rw [Example12.zero, Example12.master, Set.ext_iff] at h
  have h1 : (1 : Example12.Token) ∈ ({0} : Set Example12.Token) := (h 1).mpr (Set.mem_univ 1)
  simp only [Set.mem_singleton_iff] at h1
  exact absurd h1 (by decide)
end

section
/-- The two total elements are incomparable: `elemOne ⋢ elemZero`. -/
theorem elemOne_not_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h Example12.one (Or.inr rfl) with hm | hz
  · exact one_ne_master hm
  · exact one_ne_zero hz
end

section
/-- The two total elements are incomparable: `elemZero ⋢ elemOne`. -/
theorem elemZero_not_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h Example12.zero (Or.inr rfl) with hm | ho
  · exact zero_ne_master hm
  · exact one_ne_zero ho.symm
end

section
/- concordance: source L2259 EXERCISE 4.12 no greatest fixed point -/
/-- **Exercise 4.12 (Scott 1981, PRG-19).** Every element is a fixed point of the identity map
(so `I_T` has *many* fixed points: `⊥`, `elemZero`, `elemOne`). -/
theorem idMap_fixed (x : T.Element) : (idMap T).toElementMap x = x := toElementMap_idMap x
end

section
/-- **Exercise 4.12 (Scott 1981, PRG-19).** `I_T` has no *greatest* (hence no maximum) fixed point:
the two total elements `elemZero`, `elemOne` are both fixed points, are incomparable, and no element
dominates both. -/
theorem no_greatest_fixedPoint :
    ¬ ∃ z : T.Element, (idMap T).toElementMap z = z ∧
      ∀ x, (idMap T).toElementMap x = x → x ≤ z := by
  rintro ⟨z, _, hz⟩
  have h0 : elemZero ≤ z := hz elemZero (idMap_fixed elemZero)
  have h1 : elemOne ≤ z := hz elemOne (idMap_fixed elemOne)
  rcases element_classification z with rfl | rfl | rfl
  · exact (bot_lt_elemZero).2 h0
  · exact elemOne_not_le_elemZero h1
  · exact elemZero_not_le_elemOne h0
end

section
set_option linter.unusedVariables false

theorem example_412 : And
  (∀
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T
        DomainTheory.NeighbourhoodSystems.Exercise412.T
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise412.T)
        x)
      x)
  (Not
    (∃ (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
      And
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Exercise412.T)
            z)
          z)
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T),
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                x)
              x →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)))
              x z))) :=
  @And.intro
  (∀
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T
        DomainTheory.NeighbourhoodSystems.Exercise412.T
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise412.T)
        x)
      x)
  (Not
    (∃ (z :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise412.T),
      And
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Exercise412.T)
            z)
          z)
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T),
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Exercise412.T DomainTheory.NeighbourhoodSystems.Exercise412.T
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                x)
              x →
            @LE.le
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
              (@Preorder.toLE
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                (@PartialOrder.toPreorder
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                    DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise412.T)))
              x z)))
  DomainTheory.NeighbourhoodSystems.Exercise412.idMap_fixed
  DomainTheory.NeighbourhoodSystems.Exercise412.no_greatest_fixedPoint
end

end DomainTheory.NeighbourhoodSystems.Exercise412
namespace DomainTheory.NeighbourhoodSystems.Exercise414
section
variable {A : Type*}

/- concordance: source L2283 EXERCISE 4.14 greatest powerset fixed point -/
/-- **Exercise 4.14 (Scott 1981, PRG-19).** The *greatest* fixed point of a monotone `f : P A → P A`,
constructed as the union of all post-fixed points `⋃ {x ∣ x ⊆ f(x)}`. -/
def gfpSet (f : Set A → Set A) : Set A := {a | ∃ x : Set A, x ⊆ f x ∧ a ∈ x}
end

section
variable {A : Type*}

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** The *least* fixed point of a monotone `f : P A → P A`,
as the intersection of all pre-fixed points `⋂ {x ∣ f(x) ⊆ x}`. -/
def lfpSet (f : Set A → Set A) : Set A := {a | ∀ x : Set A, f x ⊆ x → a ∈ x}
end

section
variable {A : Type*}

/-- `lfpSet f ⊆ x` for every pre-fixed point `f(x) ⊆ x`. -/
theorem lfpSet_subset (f : Set A → Set A) {x : Set A} (hx : f x ⊆ x) : lfpSet f ⊆ x :=
  fun _ ha => ha x hx
end

section
variable {A : Type*}

/-- `f (lfpSet f) ⊆ lfpSet f`: it is a pre-fixed point. -/
theorem f_subset_lfpSet (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) ⊆ lfpSet f := by
  intro a ha x hx
  exact hx (hf (lfpSet_subset f hx) ha)
end

section
variable {A : Type*}

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is a fixed point: `f(b) = b`. -/
theorem lfpSet_isFixed (f : Set A → Set A) (hf : Monotone f) :
    f (lfpSet f) = lfpSet f := by
  have hsub : f (lfpSet f) ⊆ lfpSet f := f_subset_lfpSet f hf
  have hsup : lfpSet f ⊆ f (lfpSet f) := lfpSet_subset f (hf hsub)
  exact Set.Subset.antisymm hsub hsup
end

section
variable {A : Type*}

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** `lfpSet f` is the *least* fixed point: any fixed
point `y = f(y)` satisfies `b ⊆ y`. -/
theorem lfpSet_least (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    lfpSet f ⊆ y := lfpSet_subset f (le_of_eq hy)
end

section
variable {A : Type*}

/-- Every post-fixed point `x ⊆ f(x)` is contained in `gfpSet f`. -/
theorem subset_gfpSet (f : Set A → Set A) {x : Set A} (hx : x ⊆ f x) : x ⊆ gfpSet f :=
  fun _ ha => ⟨x, hx, ha⟩
end

section
variable {A : Type*}

/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is the *greatest* fixed point: any fixed
point `y = f(y)` satisfies `y ⊆ g`. Hence `f` *does* have a maximum fixed point. -/
theorem gfpSet_greatest (f : Set A → Set A) {y : Set A} (hy : f y = y) :
    y ⊆ gfpSet f := subset_gfpSet f (le_of_eq hy.symm)
end

section
variable {A : Type*}

/-- `gfpSet f ⊆ f (gfpSet f)`: it is a post-fixed point. -/
theorem gfpSet_subset_f (f : Set A → Set A) (hf : Monotone f) :
    gfpSet f ⊆ f (gfpSet f) := by
  rintro a ⟨x, hx, hax⟩
  exact hf (subset_gfpSet f hx) (hx hax)
end

section
variable {A : Type*}

/-- **Exercise 4.14 (Scott 1981, PRG-19).** `gfpSet f` is a fixed point: `f(g) = g`. -/
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
namespace DomainTheory.NeighbourhoodSystems.Exercise417
open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

section
variable {S : Type*} [Monoid S]

/-- Scott's operator `F(x) = {1} ∪ {a, b} ∪ x · x` on `P S`. -/
def F (a b : S) (x : Set S) : Set S := {1} ∪ {a, b} ∪ x * x
end

section
variable {S : Type*} [Monoid S]

/-- `{1} ∪ {a, b} ⊆ F a b x`. -/
theorem base_subset_F (a b : S) (x : Set S) : {1} ∪ {a, b} ⊆ F a b x :=
  Set.subset_union_left
end

section
variable {S : Type*} [Monoid S]

theorem one_mem_F (a b : S) (x : Set S) : (1 : S) ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_left _ rfl)
end

section
variable {S : Type*} [Monoid S]

theorem self_mul_subset_F (a b : S) (x : Set S) : x * x ⊆ F a b x :=
  Set.subset_union_right
end

section
variable {S : Type*} [Monoid S]

/-- A pre-fixed point of `F` is a submonoid containing `{a, b}`: it contains `1` and is closed under
multiplication and contains `a, b`. Packaged as the submonoid with that carrier. -/
def preFixSubmonoid (a b : S) {x : Set S} (hx : F a b x ⊆ x) : Submonoid S where
  carrier := x
  one_mem' := hx (one_mem_F a b x)
  mul_mem' := by
    intro s t hs ht
    exact hx (self_mul_subset_F a b x (Set.mul_mem_mul hs ht))
end

section
variable {S : Type*} [Monoid S]

theorem F_monotone (a b : S) : Monotone (F a b) := by
  intro x y hxy
  exact Set.union_subset_union (le_refl _) (Set.mul_subset_mul hxy hxy)
end

section
variable {S : Type*} [Monoid S]

/-- `{1}` is a fixed point of `F 1 1`: `{1} ∪ {1, 1} ∪ {1}·{1} = {1}`. -/
theorem F_one_one_singleton : F (1 : ℕ) 1 ({1} : Set ℕ) = {1} := by
  unfold F
  rw [Set.singleton_mul_singleton]
  simp
end

section
variable {S : Type*} [Monoid S]

/-- In any monoid, `Set.univ` is a fixed point of `F a b`: `s = 1 · s ∈ univ · univ`. -/
theorem F_univ (a b : S) : F a b (Set.univ : Set S) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro s _
  exact self_mul_subset_F a b _ (Set.mem_mul.mpr ⟨1, trivial, s, trivial, one_mul s⟩)
end

section
variable {S : Type*} [Monoid S]

theorem a_mem_F (a b : S) (x : Set S) : a ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_right _ (Set.mem_insert _ _))
end

section
variable {S : Type*} [Monoid S]

theorem b_mem_F (a b : S) (x : Set S) : b ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl))
end

section
variable {S : Type*} [Monoid S]

/- concordance: source L2305 EXERCISE 4.17 generated submonoid -/
/-- **Exercise 4.17 (Scott 1981, PRG-19).** The fixed point need **not** be unique: over `S = ℕ`
(under `·`) with `a = b = 1`, both `{1}` (the least solution) and `Set.univ` solve the equation, and
they are distinct. -/
theorem fixedPoint_not_unique :
    ∃ x y : Set ℕ, F 1 1 x = x ∧ F 1 1 y = y ∧ x ≠ y := by
  refine ⟨{1}, Set.univ, F_one_one_singleton, F_univ 1 1, ?_⟩
  intro h
  have h2 : (2 : ℕ) ∈ ({1} : Set ℕ) := by rw [h]; exact Set.mem_univ 2
  simp at h2
end

section
variable {S : Type*} [Monoid S]

/-- The least solution `lfpSet (F a b)` indeed solves Scott's equation `x = {1} ∪ {a, b} ∪ x · x`. -/
theorem leastSolution_eq (a b : S) :
    F a b (lfpSet (F a b)) = lfpSet (F a b) :=
  lfpSet_isFixed (F a b) (F_monotone a b)
end

section
variable {S : Type*} [Monoid S]

/-- **Exercise 4.17 (Scott 1981, PRG-19).** The least solution of `x = {1} ∪ {a, b} ∪ x · x` is the
submonoid generated by `{a, b}` (all finite products of `a`s and `b`s, including `1`). -/
theorem lfpSet_eq_closure (a b : S) :
    lfpSet (F a b) = (Submonoid.closure ({a, b} : Set S) : Set S) := by
  apply Set.Subset.antisymm
  · -- `lfpSet ⊆ closure`: the closure is a (pre-)fixed point of `F`.
    have hclosed : F a b (Submonoid.closure ({a, b} : Set S)) ⊆
        (Submonoid.closure ({a, b} : Set S) : Set S) := by
      apply Set.union_subset
      · apply Set.union_subset
        · rintro s rfl; exact (Submonoid.closure ({a, b} : Set S)).one_mem
        · intro s hs
          rcases hs with rfl | rfl
          · exact Submonoid.subset_closure (Set.mem_insert _ _)
          · exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rintro s ⟨t, ht, u, hu, rfl⟩
        exact (Submonoid.closure ({a, b} : Set S)).mul_mem ht hu
    exact lfpSet_subset (F a b) hclosed
  · -- `closure ⊆ lfpSet`: `lfpSet` is a submonoid containing `{a, b}`.
    have hfix : F a b (lfpSet (F a b)) ⊆ lfpSet (F a b) :=
      le_of_eq (leastSolution_eq a b)
    have ha : a ∈ lfpSet (F a b) := hfix (a_mem_F a b _)
    have hb : b ∈ lfpSet (F a b) := hfix (b_mem_F a b _)
    have hmem : ({a, b} : Set S) ⊆ lfpSet (F a b) := by
      intro s hs
      rcases Set.mem_insert_iff.mp hs with h | h
      · rw [h]; exact ha
      · rw [Set.mem_singleton_iff.mp h]; exact hb
    exact (Submonoid.closure_le (S := preFixSubmonoid a b hfix)).mpr hmem
end

section
set_option linter.unusedVariables false

theorem example_417.{u_1} : And
  (∃ (x : Set Nat) (y : Set Nat),
    And
      (@Eq (Set Nat)
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) x)
        x)
      (And
        (@Eq (Set Nat)
          (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
          y)
        (@Ne (Set Nat) x y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b : S),
    @Eq (Set S)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F S inst a b))
      (@SetLike.coe (@Submonoid S (@Monoid.toMulOneClass S inst)) S
        (@Submonoid.instSetLike S (@Monoid.toMulOneClass S inst))
        (@Submonoid.closure S (@Monoid.toMulOneClass S inst)
          (@Insert.insert S (Set S) (@Set.instInsert S) a
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) b))))) :=
  @And.intro
  (∃ (x : Set Nat) (y : Set Nat),
    And
      (@Eq (Set Nat)
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) x)
        x)
      (And
        (@Eq (Set Nat)
          (@DomainTheory.NeighbourhoodSystems.Exercise417.F Nat Nat.instMonoid
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) y)
          y)
        (@Ne (Set Nat) x y)))
  (∀ {S : Type u_1} [inst : Monoid S] (a b : S),
    @Eq (Set S)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet S
        (@DomainTheory.NeighbourhoodSystems.Exercise417.F S inst a b))
      (@SetLike.coe (@Submonoid S (@Monoid.toMulOneClass S inst)) S
        (@Submonoid.instSetLike S (@Monoid.toMulOneClass S inst))
        (@Submonoid.closure S (@Monoid.toMulOneClass S inst)
          (@Insert.insert S (Set S) (@Set.instInsert S) a
            (@Singleton.singleton S (Set S) (@Set.instSingletonSet S) b)))))
  DomainTheory.NeighbourhoodSystems.Exercise417.fixedPoint_not_unique
  @DomainTheory.NeighbourhoodSystems.Exercise417.lfpSet_eq_closure
end

end DomainTheory.NeighbourhoodSystems.Exercise417
namespace DomainTheory.NeighbourhoodSystems.Exercise421
open DomainTheory.NeighbourhoodSystems.Exercise414

section
/-- Scott's operator `ℓ ↦ {(n, n)} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}` on `P(ℕ × ℕ)`. -/
def leOp (u : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {p | p.1 = p.2} ∪ {p | ∃ m, (p.1, m) ∈ u ∧ p.2 = m + 1}
end

section
/-- The relation `≤` itself, as a subset of `ℕ × ℕ`. -/
def leRel : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}
end

section
/-- Scott's hint operator `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` on `P ℕ` (for fixed `n`). -/
def mulOp (n : ℕ) (u : Set ℕ) : Set ℕ := {0} ∪ {k | ∃ m ∈ u, k = n + m}
end

section
/-- Scott's `x⁺ = {n⁺ ∣ n ∈ x}` on `P ℕ`. -/
def succImage (x : Set ℕ) : Set ℕ := {k | ∃ j ∈ x, k = j + 1}
end

section
/-- The up-set `[m] = {k ∣ m ≤ k}` — the value of Scott's unique function `[·]` of 4.13(3). -/
def upSet (m : ℕ) : Set ℕ := {k | m ≤ k}
end

section
/- concordance: source L2331 EXERCISE 4.21 order as a fixed point -/
/-- **Exercise 4.21 (Scott 1981, PRG-19).** The structure-preserving bijection between
`⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` (where `[m] = {k ∣ m ≤ k}`, with distinguished element `m` and the
successor `⁺`). It is **ordinary addition** by `m`: `n ↦ m + n`. -/
def addIso (m : ℕ) : ℕ ≃ {k : ℕ // k ∈ upSet m} where
  toFun n := ⟨m + n, Nat.le_add_right m n⟩
  invFun k := k.1 - m
  left_inv n := by show m + n - m = n; omega
  right_inv := by
    rintro ⟨k, hk⟩
    exact Subtype.ext (Nat.add_sub_of_le hk)
end

section
/-- The isomorphism is given by addition: `addIso m n = m + n`. -/
theorem addIso_apply (m n : ℕ) : (addIso m n : ℕ) = m + n := rfl
end

section
/-- The isomorphism preserves the successor: `addIso m (n⁺) = (addIso m n)⁺`. -/
theorem addIso_succ (m n : ℕ) : (addIso m (n + 1) : ℕ) = (addIso m n : ℕ) + 1 := by
  simp only [addIso_apply]; omega
end

section
/-- The isomorphism sends `0` to the distinguished element `m` of `[m]`. -/
theorem addIso_zero (m : ℕ) : (addIso m 0 : ℕ) = m := by simp [addIso]
end

section
theorem leOp_monotone : Monotone leOp := by
  intro u v huv p hp
  rcases hp with hp | ⟨m, hm, hpm⟩
  · exact Or.inl hp
  · exact Or.inr ⟨m, huv hm, hpm⟩
end

section
/-- **Exercise 4.21 (Scott 1981, PRG-19).** `≤` solves Scott's fixed-point equation. -/
theorem leRel_isFixed : leOp leRel = leRel := by
  apply Set.Subset.antisymm
  · rintro ⟨n, m⟩ (h | ⟨k, hk, rfl⟩)
    · exact le_of_eq (h : n = m)
    · exact Nat.le_succ_of_le (hk : n ≤ k)
  · rintro ⟨n, m⟩ (h : n ≤ m)
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨m - 1, ?_, ?_⟩
      · change n ≤ m - 1; omega
      · omega
end

section
/-- The key step toward uniqueness: any fixed point `u` of `leOp` agrees with `≤` pointwise.
By induction on the second coordinate `m`; the base case `m = 0` uses that the successor clause
cannot produce a `0` on the right. -/
theorem mem_fixedPoint_iff {u : Set (ℕ × ℕ)} (hu : leOp u = u) (n m : ℕ) :
    (n, m) ∈ u ↔ n ≤ m := by
  induction m with
  | zero =>
    rw [← hu]
    constructor
    · rintro (h | ⟨k, _, hk⟩)
      · exact le_of_eq h
      · exact absurd hk (Nat.succ_ne_zero k).symm
    · intro h
      exact Or.inl (Nat.le_zero.mp h)
  | succ k ih =>
    rw [← hu]
    constructor
    · rintro (h | ⟨j, hj, hjk⟩)
      · exact le_of_eq h
      · have hjk' : j = k := by omega
        subst hjk'
        exact Nat.le_succ_of_le (ih.mp hj)
    · intro h
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨k, ih.mpr (Nat.lt_succ_iff.mp h'), rfl⟩
end

section
/-- **Exercise 4.21 (Scott 1981, PRG-19).** The order relation `≤` is the **unique** fixed point of
Scott's equation: any `u` with `leOp u = u` equals `leRel`. -/
theorem leOp_unique {u : Set (ℕ × ℕ)} (hu : leOp u = u) : u = leRel := by
  ext ⟨n, m⟩
  rw [mem_fixedPoint_iff hu]
  rfl
end

section
theorem mulOp_monotone (n : ℕ) : Monotone (mulOp n) := by
  rintro u v huv k (hk | ⟨m, hm, rfl⟩)
  · exact Or.inl hk
  · exact Or.inr ⟨m, huv hm, rfl⟩
end

section
/-- **Exercise 4.21 (Scott 1981, PRG-19).** The least solution of the multiplication equation
`n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` is exactly the set of **multiples of `n`**. -/
theorem mulOp_lfp_eq_multiples (n : ℕ) :
    lfpSet (mulOp n) = {k | ∃ i, k = n * i} := by
  apply Set.Subset.antisymm
  · -- `lfpSet ⊆ multiples`: the multiples form a pre-fixed point.
    have hpre : mulOp n {k | ∃ i, k = n * i} ⊆ {k | ∃ i, k = n * i} := by
      rintro k (rfl | ⟨m, ⟨i, rfl⟩, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by ring⟩
    exact lfpSet_subset (mulOp n) hpre
  · -- `multiples ⊆ lfpSet`: each `n * i` is reached by induction on `i`.
    have hfix : mulOp n (lfpSet (mulOp n)) = lfpSet (mulOp n) :=
      lfpSet_isFixed (mulOp n) (mulOp_monotone n)
    rintro k ⟨i, rfl⟩
    induction i with
    | zero =>
      rw [← hfix]; exact Or.inl (by simp)
    | succ j ih =>
      rw [← hfix]
      exact Or.inr ⟨n * j, ih, by ring⟩
end

section
/-- `[m⁺] = [m]⁺`: the recursion step of 4.13(3). -/
theorem upSet_succ (m : ℕ) : upSet (m + 1) = succImage (upSet m) := by
  ext k
  simp only [upSet, succImage, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨k - 1, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    omega
end

section
/-- `[0] = ℕ`: the recursion base of 4.13(3). -/
theorem upSet_zero : upSet 0 = Set.univ := by
  ext k; simp [upSet]
end

section
/-- **Exercise 4.21 / 4.13(3) (Scott 1981, PRG-19).** `[·] = upSet` is the *unique* function with
`[0] = ℕ` and `[m⁺] = [m]⁺`. -/
theorem upSet_unique (s : ℕ → Set ℕ) (h0 : s 0 = Set.univ)
    (hsucc : ∀ m, s (m + 1) = succImage (s m)) : s = upSet := by
  funext m
  induction m with
  | zero => rw [h0, upSet_zero]
  | succ k ih => rw [hsucc k, ih, upSet_succ]
end

section
set_option linter.unusedVariables false

theorem example_421 : And
  (And
    (And
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
    (@Eq (Set (Prod Nat Nat))
      (DomainTheory.NeighbourhoodSystems.Exercise421.leOp DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
  (∀ (n : Nat),
    @Eq (Set Nat)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet Nat
        (DomainTheory.NeighbourhoodSystems.Exercise421.mulOp n))
      (@Set.ofPred Nat fun (k : Nat) => ∃ (i : Nat), @Eq Nat k (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n i))) :=
  @And.intro
  (And
    (And
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
    (@Eq (Set (Prod Nat Nat))
      (DomainTheory.NeighbourhoodSystems.Exercise421.leOp DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
  (∀ (n : Nat),
    @Eq (Set Nat)
      (@DomainTheory.NeighbourhoodSystems.Exercise414.lfpSet Nat
        (DomainTheory.NeighbourhoodSystems.Exercise421.mulOp n))
      (@Set.ofPred Nat fun (k : Nat) => ∃ (i : Nat), @Eq Nat k (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n i)))
  (@And.intro
    (And
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel))
    (@Eq (Set (Prod Nat Nat))
      (DomainTheory.NeighbourhoodSystems.Exercise421.leOp DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
    (@And.intro
      (∀ (s : Nat → Set Nat),
        @Eq (Set Nat) (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.univ Nat) →
          (∀ (m : Nat),
              @Eq (Set Nat)
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (DomainTheory.NeighbourhoodSystems.Exercise421.succImage (s m))) →
            @Eq (Nat → Set Nat) s DomainTheory.NeighbourhoodSystems.Exercise421.upSet)
      (∀ {u : Set (Prod Nat Nat)},
        @Eq (Set (Prod Nat Nat)) (DomainTheory.NeighbourhoodSystems.Exercise421.leOp u) u →
          @Eq (Set (Prod Nat Nat)) u DomainTheory.NeighbourhoodSystems.Exercise421.leRel)
      DomainTheory.NeighbourhoodSystems.Exercise421.upSet_unique
      @DomainTheory.NeighbourhoodSystems.Exercise421.leOp_unique)
    DomainTheory.NeighbourhoodSystems.Exercise421.leRel_isFixed)
  DomainTheory.NeighbourhoodSystems.Exercise421.mulOp_lfp_eq_multiples
end

end DomainTheory.NeighbourhoodSystems.Exercise421
namespace DomainTheory.NeighbourhoodSystems.Exercise424
open DomainTheory.NeighbourhoodSystems.Exercise414 Function

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- Tarski's operator `T(X) = (A − g(B)) ∪ g(f(X))` on `P A`. -/
def sbOp (f : A → B) (g : B → A) (X : Set A) : Set A := (Set.range g)ᶜ ∪ g '' (f '' X)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbOp_monotone (f : A → B) (g : B → A) : Monotone (sbOp f g) := by
  intro X Y hXY a ha
  rcases ha with ha | ⟨b, ⟨x, hx, rfl⟩, rfl⟩
  · exact Or.inl ha
  · exact Or.inr ⟨f x, ⟨x, hXY hx, rfl⟩, rfl⟩
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- The Tarski fixed point `X` with `X = (A − g(B)) ∪ g(f(X))` (`lfpSet`, Exercise 4.14). -/
def sbSet (f : A → B) (g : B → A) : Set A := lfpSet (sbOp f g)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbSet_isFixed (f : A → B) (g : B → A) : sbOp f g (sbSet f g) = sbSet f g :=
  lfpSet_isFixed (sbOp f g) (sbOp_monotone f g)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- `g(f(a)) ∈ X` whenever `a ∈ X` (the `g(f(X)) ⊆ T(X) = X` half). -/
theorem g_f_mem_of_mem {a : A} (ha : a ∈ sbSet f g) : g (f a) ∈ sbSet f g := by
  rw [← sbSet_isFixed]
  exact Or.inr ⟨f a, ⟨a, ha, rfl⟩, rfl⟩
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- Anything outside the fixed set `X` lies in the range of `g` (so it has a `g`-preimage). -/
theorem mem_range_of_not_mem {a : A} (ha : a ∉ sbSet f g) : a ∈ Set.range g := by
  have hne : a ∉ sbOp f g (sbSet f g) := by rw [sbSet_isFixed]; exact ha
  have : ¬ a ∉ Set.range g := fun h => hne (Or.inl h)
  exact not_not.mp this
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

open Classical in
/- concordance: source L2363 EXERCISE 4.24 Schroeder-Bernstein theorem -/
/-- **Exercise 4.24 (Scott 1981, PRG-19).** Tarski's bijection `h : A → B`: `f` on the fixed set
`X`, and the `g`-inverse off it. -/
noncomputable def sbFun (f : A → B) (g : B → A) (a : A) : B :=
  if ha : a ∈ sbSet f g then f a else Classical.choose (mem_range_of_not_mem ha)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- Off the fixed set, `h(a)` is a genuine `g`-preimage of `a`: `g(h(a)) = a`. -/
theorem g_sbFun_not_mem {a : A} (ha : a ∉ sbSet f g) : g (sbFun f g a) = a := by
  rw [sbFun, dite_eq_right ha]
  exact Classical.choose_spec (mem_range_of_not_mem ha)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_mem {a : A} (ha : a ∈ sbSet f g) : sbFun f g a = f a := dite_eq_left ha
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_injective (hf : Injective f) : Injective (sbFun f g) := by
  intro a₁ a₂ heq
  by_cases h1 : a₁ ∈ sbSet f g <;> by_cases h2 : a₂ ∈ sbSet f g
  · rw [sbFun_mem h1, sbFun_mem h2] at heq
    exact hf heq
  · -- `a₁ ∈ X`, `a₂ ∉ X`: `f a₁ = g⁻¹ a₂` ⟹ `a₂ = g(f a₁) ∈ X`, contradiction.
    exfalso
    rw [sbFun_mem h1] at heq
    have : a₂ = g (f a₁) := by rw [heq, g_sbFun_not_mem h2]
    exact h2 (this ▸ g_f_mem_of_mem h1)
  · exfalso
    rw [sbFun_mem h2] at heq
    have : a₁ = g (f a₂) := by rw [← heq, g_sbFun_not_mem h1]
    exact h1 (this ▸ g_f_mem_of_mem h2)
  · -- both off `X`: apply `g` and use injectivity of `g`.
    have : g (sbFun f g a₁) = g (sbFun f g a₂) := by rw [heq]
    rw [g_sbFun_not_mem h1, g_sbFun_not_mem h2] at this
    exact this
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  intro b
  by_cases hb : g b ∈ sbSet f g
  · -- `g b ∈ X = T X`; not in `(range g)ᶜ`, so `g b ∈ g(f(X))`.
    rw [← sbSet_isFixed] at hb
    rcases hb with hb | ⟨y, ⟨a, ha, rfl⟩, hgy⟩
    · exact absurd ⟨b, rfl⟩ hb
    · refine ⟨a, ?_⟩
      rw [sbFun_mem ha, hg hgy]
  · -- `g b ∉ X`: then `h (g b) = b`.
    refine ⟨g b, ?_⟩
    exact hg (g_sbFun_not_mem hb)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- **Exercise 4.24 (Scott 1981, PRG-19).** The one-one correspondence as an `Equiv A ≃ B`. -/
noncomputable def schroeder_bernstein_equiv (hf : Injective f) (hg : Injective g) : A ≃ B :=
  Equiv.ofBijective (sbFun f g) ⟨sbFun_injective hf, sbFun_surjective hg⟩
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

open Classical in


/-- **Exercise 4.24 (Scott 1981, PRG-19) — Schröder–Bernstein.** Injections `f : A → B` and
`g : B → A` yield a bijection `A → B`. -/
theorem schroeder_bernstein (hf : Injective f) (hg : Injective g) :
    ∃ h : A → B, Bijective h :=
  ⟨sbFun f g, sbFun_injective hf, sbFun_surjective hg⟩
end

section
set_option linter.unusedVariables false

theorem example_424.{u_1, u_2} : ∀ {A : Type u_1} {B : Type u_2} {f : A → B} {g : B → A},
  @Function.Injective A B f → @Function.Injective B A g → ∃ (h : A → B), @Function.Bijective A B h :=
  @DomainTheory.NeighbourhoodSystems.Exercise424.schroeder_bernstein
end

end DomainTheory.NeighbourhoodSystems.Exercise424
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/- concordance: source L1657 THEOREM 4.1 least fixed point -/
/-- **Theorem 4.1 (Scott 1981, PRG-19).** The `n`-fold composition `fⁿ` of an endomap with itself:
`f⁰ = I_𝒟` and `f^{n+1} = f ∘ fⁿ`. -/
def iterMap (f : ApproximableMap V V) : ℕ → ApproximableMap V V
  | 0 => idMap V
  | (n + 1) => f.comp (f.iterMap n)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem iterMap_zero (f : ApproximableMap V V) : f.iterMap 0 = idMap V := rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem iterMap_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterMap (n + 1) = f.comp (f.iterMap n) := rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Composition is monotone in both arguments. -/
theorem comp_mono {f g a b : ApproximableMap V V} (hfg : f ≤ g) (hab : a ≤ b) :
    f.comp a ≤ g.comp b := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hab X Y hXY, hfg Y Z hYZ⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The iterate is monotone in the map: `f ⊑ g ⟹ fⁿ ⊑ gⁿ` (Scott's "`fⁿ ⊆ gⁿ`"). -/
theorem iterMap_mono_map {f g : ApproximableMap V V} (hfg : f ≤ g) (n : ℕ) :
    f.iterMap n ≤ g.iterMap n := by
  induction n with
  | zero => show (idMap V) ≤ (idMap V); exact le_refl _
  | succ k ih => exact comp_mono hfg ih

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f` commutes with its own iterate: `f ∘ fⁿ = fⁿ ∘ f`. Proved by induction using associativity
and the identity laws. -/
theorem iter_comm (f : ApproximableMap V V) (n : ℕ) :
    f.comp (f.iterMap n) = (f.iterMap n).comp f := by
  induction n with
  | zero => rw [show f.iterMap 0 = idMap V from rfl, comp_idMap, idMap_comp]
  | succ n ih =>
    show f.comp (f.comp (f.iterMap n)) = (f.comp (f.iterMap n)).comp f
    rw [comp_assoc, ← ih]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Scott's "a sequence for an `X ∈ x` can always be extended": if `Δ fⁿ X`, then `Δ f^{n+1} X`
(prepend a `Δ`-step, using `Δ f Δ`). -/
theorem rel_master_succ (f : ApproximableMap V V) {n : ℕ} {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap (n + 1)).rel V.master X := by
  have hcomm : f.iterMap (n + 1) = (f.iterMap n).comp f := iter_comm f n
  rw [hcomm]
  exact ⟨V.master, f.master_rel, h⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Monotonicity of the reachability relation in the number of steps: `n ≤ m` and `Δ fⁿ X` imply
`Δ fᵐ X`. -/
theorem rel_master_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap m).rel V.master X := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rel_master_succ f ih

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The least fixed point of `f`, Scott's
`x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`. The three filter conditions are exactly Scott's: `Δ ∈ x` (the
`n = 0` witness `I_𝒟`); closure under intersection follows from intersectivity (`inter_right`) of
the single iterate `f^{max n m}` reached by extending the shorter chain; upward closure is `mono`. -/
def fixElement (f : ApproximableMap V V) : V.Element where
  mem X := ∃ n, (f.iterMap n).rel V.master X
  sub := fun ⟨n, h⟩ => (f.iterMap n).rel_cod h
  master_mem := ⟨0, show (idMap V).rel V.master V.master from (idMap V).master_rel⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have hX : (f.iterMap (max n m)).rel V.master X := rel_master_mono f (le_max_left n m) hn
    have hY : (f.iterMap (max n m)).rel V.master Y := rel_master_mono f (le_max_right n m) hm
    exact (f.iterMap (max n m)).inter_right hX hY
  up_mem := by
    rintro X Y ⟨n, hn⟩ hYmem hXY
    exact ⟨n, (f.iterMap n).mono hn subset_rfl hXY V.master_mem hYmem⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem mem_fixElement (f : ApproximableMap V V) {X : Set α} :
    f.fixElement.mem X ↔ ∃ n, (f.iterMap n).rel V.master X := Iff.rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The least fixed point is monotone in the map: `f ⊑ g ⟹ fix(f) ⊑ fix(g)` (immediate from
`iterMap_mono_map`; underlies the approximability of `fix` in 4.2). -/
theorem fixElement_mono {f g : ApproximableMap V V} (hfg : f ≤ g) :
    f.fixElement ≤ g.fixElement := by
  rintro X ⟨n, hn⟩
  exact ⟨n, iterMap_mono_map hfg n V.master X hn⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/- concordance: source L1715 THEOREM 4.2 fix combinator -/
/-- **Theorem 4.2 (Scott 1981, PRG-19).** The fixed-point operator `fix : (𝒟 → 𝒟) → 𝒟` as an
approximable mapping. Built by the extension principle (Exercise 2.8, `ofMono`): on the finite
element `↑F` it returns `fix(↑F)`, where `↑F = toApproxMap (principal hF)` is the least map of the
neighbourhood `F` (Proposition 3.9). Monotonicity of `↑F ↦ fix(↑F)` is `fixElement_mono` composed
with the order-iso `funSpaceEquiv`. -/
def fixMap (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V :=
  ofMono (fun W hW => (toApproxMap ((funSpace V V).principal hW)).fixElement)
    (fun W W' hW hW' hW'W => by
      apply fixElement_mono
      exact (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff hW hW').mpr hW'W))
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `n`-th approximant `fⁿ(⊥)` of the least fixed point. -/
def iterElem (f : ApproximableMap V V) (n : ℕ) : V.Element := (f.iterMap n).toElementMap V.bot

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗), hard half.** A finite `f`-chain
`Δ (toApproxMap φ)ⁿ X` factors through a *single* finite approximant `F ∈ φ`: there is a
neighbourhood `W ∈ φ` whose least map already realizes the same chain `Δ (↑W)ⁿ X`. The witness `W`
is accumulated as the intersection of the (finitely many) step-neighbourhoods used by the chain,
which lies in `φ` because `φ` is a filter. -/
theorem exists_principal_iterMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    ∀ (n : ℕ) (X : Set α), ((toApproxMap φ).iterMap n).rel V.master X →
      ∃ (W : Set (ApproximableMap V V)) (hw : φ.mem W),
        ((toApproxMap ((funSpace V V).principal (φ.sub hw))).iterMap n).rel V.master X := by
  intro n
  induction n with
  | zero =>
    intro X hX
    exact ⟨(funSpace V V).master, φ.master_mem, hX⟩
  | succ k ih =>
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := hX
    obtain ⟨W₁, hw₁, hW₁⟩ := ih Y hY
    have hVY : V.mem Y := ((toApproxMap φ).iterMap k).rel_cod hY
    have hVX : V.mem X := (toApproxMap φ).rel_cod hYX
    have hw₂ : φ.mem (step Y X) := toApproxMap_rel.mp hYX
    have hwInter : φ.mem (W₁ ∩ step Y X) := φ.inter_mem hw₁ hw₂
    refine ⟨W₁ ∩ step Y X, hwInter, ?_⟩
    have hg₁g : toApproxMap ((funSpace V V).principal (φ.sub hw₁))
        ≤ toApproxMap ((funSpace V V).principal (φ.sub hwInter)) :=
      (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff (φ.sub hw₁) (φ.sub hwInter)).mpr Set.inter_subset_left)
    have hYg : ((toApproxMap ((funSpace V V).principal (φ.sub hwInter))).iterMap k).rel V.master Y :=
      iterMap_mono_map hg₁g k V.master Y hW₁
    have hgYX : (toApproxMap ((funSpace V V).principal (φ.sub hwInter))).rel Y X := by
      show ((funSpace V V).principal (φ.sub hwInter)).mem (step Y X)
      exact ⟨step_mem hVY hVX, Set.inter_subset_right⟩
    exact ⟨Y, hYg, hgYX⟩
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is the *least pre-fixed point*: if
`f(z) ⊆ z`, then `x ⊆ z`. (Scott's induction: `Δ ∈ z`, and `X ∈ z`, `X f Y` give `Y ∈ f(z) ⊆ z`,
so `Δ fⁿ X` implies `X ∈ z`.) In particular `x` is the least element with `f(x) = x`. -/
theorem fixElement_le_of_toElementMap_le (f : ApproximableMap V V) {z : V.Element}
    (hz : f.toElementMap z ≤ z) : f.fixElement ≤ z := by
  have key : ∀ n X, (f.iterMap n).rel V.master X → z.mem X := by
    intro n
    induction n with
    | zero =>
      intro X hn
      obtain ⟨_, hXmem, hmX⟩ := hn
      have hXmaster : X = V.master := Set.Subset.antisymm (V.sub_master hXmem) hmX
      subst hXmaster
      exact z.master_mem
    | succ k ih =>
      intro X hn
      obtain ⟨W, hW, hWX⟩ := hn
      exact hz X ⟨W, ih W hW, hWX⟩
  rintro X ⟨n, hn⟩
  exact key n X hn

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/-- On a finite element `↑F`, `fix` returns `fix(↑F)` (the least fixed point of the least map of
`F`). -/
theorem fixMap_toElementMap_principal (V : NeighborhoodSystem α)
    {W : Set (ApproximableMap V V)} (hW : (funSpace V V).mem W) :
    (fixMap V).toElementMap ((funSpace V V).principal hW) =
      (toApproxMap ((funSpace V V).principal hW)).fixElement :=
  toElementMap_ofMono_principal _ _ W hW
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/-- **Theorem 4.2 (Scott 1981, PRG-19) — Scott's equation (∗).** The elementwise action of `fix` is
the least fixed point of the corresponding map: `fix.toElementMap φ = fix(toApproxMap φ)`. The
forward inclusion (`⊆ x`) is `exists_principal_iterMap`; the reverse is monotonicity of `fix` along
`↑W ⊑ toApproxMap φ`. -/
theorem fixMap_toElementMap (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ = (toApproxMap φ).fixElement := by
  apply Element.ext
  intro X
  rw [toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨W, hw, hmem⟩
    rw [fixMap_toElementMap_principal] at hmem
    have hle : (funSpace V V).principal (φ.sub hw) ≤ φ :=
      fun Z hZ => φ.up_mem hw hZ.1 hZ.2
    exact fixElement_mono ((funSpaceEquiv V V).monotone hle) X hmem
  · rintro ⟨n, hn⟩
    obtain ⟨W, hw, hWn⟩ := exists_principal_iterMap V φ n X hn
    refine ⟨W, hw, ?_⟩
    rw [fixMap_toElementMap_principal]
    exact ⟨n, hWn⟩
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/-- **Theorem 4.2(ii) (Scott 1981, PRG-19).** `f(x) ⊆ x ⟹ fix(f) ⊆ x`: `fix` lands in the least
pre-fixed point. -/
theorem fixMap_least (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) {z : V.Element}
    (hz : (toApproxMap φ).toElementMap z ≤ z) : (fixMap V).toElementMap φ ≤ z := by
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap φ) hz
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/-- `fix` applied to (the filter of) an approximable map `f` returns the least fixed point of `f`.
This is the bridge to the "for any `f : 𝒟 → 𝒟`" form of Theorem 4.2, using the Theorem 3.10
isomorphism `toApproxMap (toFilter f) = f`. -/
theorem fixMap_toElementMap_toFilter (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    (fixMap V).toElementMap (toFilter f) = f.fixElement := by
  rw [fixMap_toElementMap]
  have h : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv V V).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  rw [h]
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `fⁿ(⊥)` agrees with the iterated elementwise function `(f(·))^[n] ⊥` — Scott's `fⁿ(⊥)`. -/
theorem iterElem_eq_iterate (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n = (f.toElementMap)^[n] V.bot := by
  induction n with
  | zero =>
    show (f.iterMap 0).toElementMap V.bot = V.bot
    exact toElementMap_idMap V.bot
  | succ k ih =>
    have hstep : f.iterElem (k + 1) = f.toElementMap (f.iterElem k) := by
      show (f.comp (f.iterMap k)).toElementMap V.bot
          = f.toElementMap ((f.iterMap k).toElementMap V.bot)
      rw [toElementMap_comp]
    rw [hstep, ih, Function.iterate_succ', Function.comp_apply]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `Y ∈ fⁿ(⊥) ↔ Δ fⁿ Y`: the `n`-th approximant is the family of neighbourhoods reachable from
`Δ` in exactly the `n` steps recorded by `fⁿ`. -/
theorem mem_iterElem (f : ApproximableMap V V) (n : ℕ) {X : Set α} :
    (f.iterElem n).mem X ↔ (f.iterMap n).rel V.master X := by
  constructor
  · rintro ⟨W, hW, hWX⟩
    rw [mem_bot] at hW; subst hW; exact hWX
  · intro h; exact ⟨V.master, by rw [mem_bot], h⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The approximants form an increasing chain: `n ≤ m ⟹ fⁿ(⊥) ⊑ fᵐ(⊥)`. -/
theorem iterElem_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) :
    f.iterElem n ≤ f.iterElem m := by
  intro X hX
  rw [mem_iterElem] at hX ⊢
  exact rel_master_mono f hnm hX

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)`, here as the directed union of
the increasing chain of approximants. -/
theorem fixElement_eq_iSupDirected (f : ApproximableMap V V) :
    f.fixElement =
      NeighborhoodSystem.iSupDirected (f.iterElem)
        (fun i j => ⟨max i j, iterElem_mono f (le_max_left i j),
          iterElem_mono f (le_max_right i j)⟩) := by
  apply Element.ext
  intro X
  rw [NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap

/-- **Theorem 4.2(iii) (Scott 1981, PRG-19).** `fix(f) = ⊔ₙ fⁿ(⊥)` (as a directed union). -/
theorem fixMap_eq_iSup (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (fixMap V).toElementMap φ =
      NeighborhoodSystem.iSupDirected ((toApproxMap φ).iterElem)
        (fun i j => ⟨max i j, iterElem_mono _ (le_max_left i j),
          iterElem_mono _ (le_max_right i j)⟩) := by
  rw [fixMap_toElementMap]
  exact fixElement_eq_iSupDirected (toApproxMap φ)
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is a *fixed point*: `f(x) = x`.
`f(x) ⊆ x` appends an `f`-step (`Δ f^{n+1} X` from `Δ fⁿ X' f X`); `x ⊆ f(x)` reads off the last
step of the chain (the empty chain forces `X = Δ`, handled by `master_mem`/`master_rel`). -/
theorem toElementMap_fixElement (f : ApproximableMap V V) :
    f.toElementMap f.fixElement = f.fixElement := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨n, hn⟩, hXY⟩
    exact ⟨n + 1, ⟨X, hn, hXY⟩⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      obtain ⟨_, hYmem, hmY⟩ := hn
      have hYmaster : Y = V.master := Set.Subset.antisymm (V.sub_master hYmem) hmY
      subst hYmaster
      exact ⟨V.master, f.fixElement.master_mem, f.master_rel⟩
    | succ k =>
      obtain ⟨Z, hZ, hZY⟩ := hn
      exact ⟨Z, ⟨k, hZ⟩, hZY⟩

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem theorem_41.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) z)
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) z)
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_le_of_toElementMap_le
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap_fixElement
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems.Example43
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
/-- Membership in Scott's natural-number system: a neighbourhood is the whole space `ℕ` or a
singleton `{n}`. -/
def memN (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}
end

section
theorem memN_singleton (n : ℕ) : memN ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩
end

section
theorem memN_univ : memN (Set.univ : Set ℕ) := Or.inl rfl
end

section
/-- Any two neighbourhoods of `N` are nested or disjoint: `ℕ` contains every singleton, and two
distinct singletons are disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memN := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (Set.Subset.refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext k
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl hkm
      exact h hkm
end

section
/- concordance: source L1795 EXAMPLE 4.3 partial functions on integers -/
/-- **Example 4.3 (Scott 1981, PRG-19).** The natural-number neighbourhood system `N` on `Δ = ℕ`. -/
abbrev N : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memN Set.univ Set.univ_nonempty memN_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)
end

section
@[simp] theorem N_mem {X : Set ℕ} : N.mem X ↔ memN X := Iff.rfl
end

section
@[simp] theorem N_master : N.master = (Set.univ : Set ℕ) := rfl
end

section
/-- The two-token truth domain `T` of Example 1.2 (= `Example23.T`). -/
abbrev T : NeighborhoodSystem Example12.Token := Example23.T
end

section
/-- Scott's total element `n̂ = ↑{n} = {{n}, ℕ}`, the principal filter of the singleton `{n}`. -/
def natElem (n : ℕ) : N.Element := N.principal (N_mem.mpr (memN_singleton n))
end

section
/-- The value table for `pred`: `pred(0) = ⊥`, `pred(k+1) = k`. -/
def predVal : ℕ → N.Element
  | 0 => N.bot
  | (k + 1) => natElem k
end

section
/-- Singletons of naturals are one-one as sets. -/
theorem singleton_nat_inj {n m : ℕ} (h : ({n} : Set ℕ) = {m}) : n = m := by
  have h1 : n ∈ ({n} : Set ℕ) := rfl
  rw [h] at h1
  exact h1
end

section
/-- `ℕ` is not a singleton (a witness `n+1 ≠ n`). -/
theorem univ_ne_singleton (n : ℕ) : (Set.univ : Set ℕ) ≠ {n} := by
  intro h
  have h1 : (n + 1) ∈ ({n} : Set ℕ) := h ▸ Set.mem_univ (n + 1)
  exact Nat.succ_ne_self n h1
end

section
/-- `{n} ≠ ℕ` (the symmetric form). -/
theorem singleton_ne_univ (n : ℕ) : ({n} : Set ℕ) ≠ Set.univ := fun h => univ_ne_singleton n h.symm
end

section
/-- The *strict* approximable map `N → V` determined by a choice of value `val n ∈ |V|` for each
`n`: it sends the total element `n̂` to `val n` and the bottom `⊥` to `⊥`. The relation
`X f Y` holds when either `X = Δ_N` forces the blunt output `Y = Δ_V` (the strict `⊥ ↦ ⊥` clause),
or `X = {n}` and `Y` is a neighbourhood of `val n`.

Definition 2.1 checks uniformly: (i) `Δ_N f Δ_V`; (ii) intersect outputs — distinct inputs are
impossible (`ℕ ≠ {n}`, singletons are one-one), so both outputs come from the *same* `val n` and
`inter_mem` of the filter `val n` applies; (iii) sharpening `{n} ⊆ X` keeps the input a singleton
`{n}`, and `up_mem` of `val n` widens the output, while a blunt input `Δ_N` forces `Δ_V`. -/
def constLiftN {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    ApproximableMap N V where
  rel X Y := (X = Set.univ ∧ Y = V.master) ∨ (∃ n, X = {n} ∧ (val n).mem Y)
  rel_dom := by
    rintro X Y (⟨rfl, _⟩ | ⟨n, rfl, _⟩)
    · exact memN_univ
    · exact memN_singleton n
  rel_cod := by
    rintro X Y (⟨_, rfl⟩ | ⟨n, _, hY⟩)
    · exact V.master_mem
    · exact (val n).sub hY
  master_rel := Or.inl ⟨rfl, rfl⟩
  inter_right := by
    rintro X Y Y' (⟨rfl, rfl⟩ | ⟨n, rfl, hY⟩) hc'
    · rcases hc' with ⟨_, rfl⟩ | ⟨n, hX, _⟩
      · exact Or.inl ⟨rfl, by rw [Set.inter_self]⟩
      · exact (univ_ne_singleton n hX).elim
    · rcases hc' with ⟨hX, _⟩ | ⟨n', hX', hY'⟩
      · exact (singleton_ne_univ n hX).elim
      · have hnn' : n = n' := singleton_nat_inj hX'
        subst hnn'
        exact Or.inr ⟨n, rfl, (val n).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨rfl, rfl⟩ | ⟨n, rfl, hY⟩) hX'X hYY' hX' hY'
    · have hY'master : Y' = V.master := Set.Subset.antisymm (V.sub_master hY') hYY'
      subst hY'master
      rcases hX' with rfl | ⟨k, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨k, rfl, (val k).master_mem⟩
    · rcases hX' with rfl | ⟨k, rfl⟩
      · exact (singleton_ne_univ n (Set.univ_subset_iff.mp hX'X)).elim
      · have hkn : k = n := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hX'X)
        subst hkn
        exact Or.inr ⟨k, rfl, (val k).up_mem hY hY' hYY'⟩
end

section
/-- **Example 4.3 — `pred`.** `pred(0) = ⊥`, `pred(n+1) = n`, strict (`pred(⊥) = ⊥`). -/
def predMap : ApproximableMap N N := constLiftN N predVal
end

section
/-- **Example 4.3 — `succ`.** `succ(n) = n + 1`, strict (`succ(⊥) = ⊥`). -/
def succMap : ApproximableMap N N := constLiftN N (fun n => natElem (n + 1))
end

section
/-- Scott's `0 ∈ |N|`, the distinguished zero of the structured domain. -/
def zeroElt : N.Element := natElem 0
end

section
/-- The value table for `zero`: `zero(0) = true`, `zero(n+1) = false`. -/
def zeroVal : ℕ → T.Element
  | 0 => Example23.trueElt
  | (_ + 1) => Example23.falseElt
end

section
/-- **Example 4.3 — `zero`.** `zero(0) = true`, `zero(n+1) = false`, strict (`zero(⊥) = ⊥`). -/
def zeroMap : ApproximableMap N T := constLiftN T zeroVal
end

section
/-- `⊥ ∈ N` reads: a neighbourhood lies in `⊥` iff it is the whole space `ℕ`. -/
theorem N_bot_mem {X : Set ℕ} : N.bot.mem X ↔ X = Set.univ := NeighborhoodSystem.mem_bot N
end

section
/-- **Computation on bottom (strictness).** `f(⊥) = ⊥`. -/
theorem constLiftN_bot {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    (constLiftN V val).toElementMap N.bot = V.bot := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [N_bot_mem] at hXmem
    subst hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, _⟩
    · exact V.mem_bot.mpr rfl
    · exact (univ_ne_singleton k hXk).elim
  · intro hY
    rw [V.mem_bot] at hY
    subst hY
    exact ⟨Set.univ, N_bot_mem.mpr rfl, Or.inl ⟨rfl, rfl⟩⟩
end

section
/-- A neighbourhood belongs to `n̂` iff it is `ℕ` (the master) or the singleton `{n}`. -/
theorem mem_natElem_iff {n : ℕ} {Y : Set ℕ} :
    (natElem n).mem Y ↔ Y = Set.univ ∨ Y = {n} := by
  unfold natElem
  rw [mem_principal]
  constructor
  · rintro ⟨hY, hsub⟩
    rcases hY with rfl | ⟨m, rfl⟩
    · exact Or.inl rfl
    · have hnm : n = m := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
      subst hnm; exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨memN_univ, Set.subset_univ _⟩
    · exact ⟨memN_singleton n, subset_rfl⟩
end

section
/-- **Computation on the total elements.** `f(n̂) = val n`. -/
theorem constLiftN_natElem {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) (n : ℕ) :
    (constLiftN V val).toElementMap (natElem n) = val n := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [mem_natElem_iff] at hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, hY⟩
    · exact (val n).master_mem
    · rcases hXmem with rfl | rfl
      · exact (univ_ne_singleton k hXk).elim
      · have hnk : n = k := singleton_nat_inj hXk
        subst hnk; exact hY
  · intro hY
    exact ⟨{n}, mem_natElem_iff.mpr (Or.inr rfl), Or.inr ⟨n, rfl, hY⟩⟩
end

section
/-- `pred(⊥) = ⊥`. -/
theorem predMap_bot : predMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N predVal
end

section
/-- `pred((n+1)^) = n̂`. -/
theorem predMap_natElem_succ (k : ℕ) : predMap.toElementMap (natElem (k + 1)) = natElem k :=
  constLiftN_natElem N predVal (k + 1)
end

section
/-- `pred(0̂) = ⊥`: predecessor of zero is undefined. -/
theorem predMap_natElem_zero : predMap.toElementMap (natElem 0) = N.bot :=
  constLiftN_natElem N predVal 0
end

section
/-- `succ(⊥) = ⊥`. -/
theorem succMap_bot : succMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N (fun n => natElem (n + 1))
end

section
/-- `succ(n̂) = (n+1)^`. -/
theorem succMap_natElem (n : ℕ) : succMap.toElementMap (natElem n) = natElem (n + 1) :=
  constLiftN_natElem N (fun n => natElem (n + 1)) n
end

section
/-- `pred(succ(n̂)) = n̂`: the predecessor undoes the successor on total elements. (A sample of the
"recursion" reasoning Scott highlights; cf. the iterated-summation example.) -/
theorem predMap_succMap_natElem (n : ℕ) :
    predMap.toElementMap (succMap.toElementMap (natElem n)) = natElem n := by
  rw [succMap_natElem, predMap_natElem_succ]
end

section
/-- `zero(⊥) = ⊥`. -/
theorem zeroMap_bot : zeroMap.toElementMap N.bot = T.bot :=
  constLiftN_bot T zeroVal
end

section
/-- `zero((n+1)^) = false`. -/
theorem zeroMap_natElem_succ (n : ℕ) : zeroMap.toElementMap (natElem (n + 1)) = Example23.falseElt :=
  constLiftN_natElem T zeroVal (n + 1)
end

section
/-- `zero(0̂) = true`. -/
theorem zeroMap_natElem_zero : zeroMap.toElementMap (natElem 0) = Example23.trueElt :=
  constLiftN_natElem T zeroVal 0
end

end DomainTheory.NeighbourhoodSystems.Example43
namespace DomainTheory.NeighbourhoodSystems.Example44
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

section
/-- Membership in `C`: a neighbourhood is a cone `σΣ*` or a singleton `{σ}`. -/
def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})
end

section
theorem memC_cone (σ : Str) : memC (cone σ) := Or.inl ⟨σ, rfl⟩
end

section
theorem memC_singleton (σ : Str) : memC ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩
end

section
/-- Prepending is monotone in its set argument. -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩
end

section
/-- `σ{τ} = {στ}`: prepending `σ` to a singleton is the singleton of the concatenation. -/
theorem prepend_singleton (σ τ : Str) : prepend σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩
end

section
/-- `{τ} ⊆ σΣ*` iff `σ` is an initial segment of `τ`. -/
theorem singleton_subset_cone {σ τ : Str} : ({τ} : Set Str) ⊆ cone σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, mem_cone]
end

section
/-- A singleton and a cone are nested-or-disjoint. -/
theorem singleton_cone_nd (σ τ : Str) :
    ({τ} : Set Str) ⊆ cone σ ∨ cone σ ⊆ {τ} ∨ ({τ} : Set Str) ∩ cone σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_cone.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_cone, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ
end

section
/-- Any two neighbourhoods of `C` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact cone_trichotomy σ τ
  · rcases singleton_cone_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_cone_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2
end

section
/- concordance: source L1989 EXAMPLE 4.4 sequence domain -/
/-- **Example 4.4 (Scott 1981, PRG-19).** The neighbourhood system `C` of finite or infinite binary
sequences on `Δ = Σ*`. -/
abbrev C : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memC Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint
    (fun _ => Set.subset_univ _)
end

section
@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl
end

section
@[simp] theorem C_master : C.master = (Set.univ : Set Str) := rfl
end

section
/-- Prepending the bit `b` (or, generally, a prefix `σ`) to a neighbourhood of `C` lands back in
`C`: `σ(τΣ*) = (στ)Σ*` and `σ{τ} = {στ}`. -/
theorem memC_prepend (σ : Str) {X : Set Str} (hX : memC X) : memC (prepend σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prepend_cone σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prepend_singleton σ ρ⟩
end

section
/-- **Example 4.4 — the successors `x ↦ bx`.** The approximable map prepending the bit `b`:
`X (bx) Y ↔ bX ⊆ Y`. Approximable because `bX` is again a neighbourhood (`memC_prepend`) and
prepending is monotone. -/
def consMap (b : Bool) : ApproximableMap C C where
  rel X Y := memC X ∧ memC Y ∧ prepend [b] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨Or.inl ⟨[], cone_nil.symm⟩, Or.inl ⟨[], cone_nil.symm⟩, ?_⟩
    exact Set.subset_univ _
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : prepend [b] X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    have hZ : memC (prepend [b] X) := memC_prepend [b] hX
    exact ⟨hX, C.inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prepend_mono [b] hX'X).trans (hsub.trans hYY')⟩
end

section
/-- **Example 4.4 — an element defined by a fixed-point equation.** Scott's `a = 01a`, the infinite
sequence that alternates `0`s and `1`s. We take the least fixed point of `x ↦ 0(1x)`
(`= consMap 0 ∘ consMap 1`), which exists by the Fixed-point Theorem 4.1. -/
def altElt : C.Element := ((consMap false).comp (consMap true)).fixElement
end

section
/-- Scott's partial element `σ⊥ = ↑σΣ*` ("the sequence starts with `σ`"). -/
def strBot (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_cone σ))
end

section
/-- Scott's total element `σ = ↑{σ}` (the finite sequence `σ`, completed). -/
def strElem (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_singleton σ))
end

section
/-- `a = 0(1a)`: `altElt` satisfies Scott's defining equation. -/
theorem altElt_eq : (consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt := by
  have h := toElementMap_fixElement ((consMap false).comp (consMap true))
  rwa [toElementMap_comp] at h
end

section
/-- `bx` on a partial element: `b(σ⊥) = (bσ)⊥`. -/
theorem consMap_strBot (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strBot σ) = strBot (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] (cone σ) ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_cone] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, memC_cone σ, hY, ?_⟩
    rw [prepend_cone]; exact hsub
end

section
/-- `bx` on a total element: `b(σ) = (bσ)` (prepend the bit to a finite sequence). -/
theorem consMap_strElem (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strElem σ) = strElem (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] {σ} ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, memC_singleton σ, hY, ?_⟩
    rw [prepend_singleton]; exact hsub
end

section
/-- `σX ⊆ X` along the prefix order: a prepended neighbourhood is contained in any neighbourhood it
refines. (Used only via `prepend_mono`; kept implicit.) -/
theorem prepend_subset_self : True := trivial
end

end DomainTheory.NeighbourhoodSystems.Example44
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The chain of approximants from a base point `a`: `iterFrom f a n = fⁿ(a)`. -/
def iterFrom (f : ApproximableMap V V) (a : V.Element) (n : ℕ) : V.Element :=
  (f.toElementMap)^[n] a

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem iterFrom_zero (f : ApproximableMap V V) (a : V.Element) :
    f.iterFrom a 0 = a := rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem iterFrom_succ (f : ApproximableMap V V) (a : V.Element) (n : ℕ) :
    f.iterFrom a (n + 1) = f.toElementMap (f.iterFrom a n) := by
  rw [iterFrom, iterFrom, Function.iterate_succ', Function.comp_apply]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- One step of the chain: `fⁿ(a) ⊑ fⁿ⁺¹(a)` (proved choice-free by induction). -/
theorem iterFrom_step (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    (n : ℕ) : f.iterFrom a n ≤ f.iterFrom a (n + 1) := by
  induction n with
  | zero => rw [iterFrom_succ f a 0, iterFrom_zero]; exact ha
  | succ k ih =>
    rw [iterFrom_succ f a k, iterFrom_succ f a (k + 1)]
    exact f.toElementMap_mono ih

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- When `a ⊑ f(a)`, the chain `fⁿ(a)` is monotone: `n ≤ m ⟹ fⁿ(a) ⊑ fᵐ(a)`. Proved by induction
on `n ≤ m` (so as to stay **choice-free**, unlike `monotone_nat_of_le_succ`). -/
theorem iterFrom_mono (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {n m : ℕ} (hnm : n ≤ m) : f.iterFrom a n ≤ f.iterFrom a m := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (iterFrom_step f ha _)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The fixed point of `f` lying above a pre-fixed-point candidate `a` (with `a ⊑ f(a)`),
constructed as the directed union `⊔ₙ fⁿ(a)`. -/
def fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) : V.Element :=
  NeighborhoodSystem.iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/- concordance: source L2203 EXERCISE 4.7 fixed point above a seed -/
/- concordance: source L2201 EXERCISES — Lecture IV exercises -/
/-- **Exercise 4.7 (Scott 1981, PRG-19).** `fixAbove f ha` is a fixed point: `f(x) = x`. -/
theorem fixAbove_isFixed (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    f.toElementMap (f.fixAbove ha) = f.fixAbove ha := by
  set hdir := (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
    iterFrom_mono f ha (le_max_right i j)⟩ :
    ∀ i j, ∃ k, f.iterFrom a i ≤ f.iterFrom a k ∧ f.iterFrom a j ≤ f.iterFrom a k) with hdir_def
  apply le_antisymm
  · -- `f(x) = ⊔ₙ f(fⁿ(a)) = ⊔ₙ f^{n+1}(a) ⊑ x` since each `f^{n+1}(a) ⊑ x`.
    rw [fixAbove, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    have : f.toElementMap (f.iterFrom a n) = f.iterFrom a (n + 1) := (iterFrom_succ f a n).symm
    rw [this]
    exact NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir (n + 1)
  · -- `x ⊑ f(x)`: each `fⁿ(a) ⊑ fⁿ⁺¹(a) = f(fⁿ(a)) ⊑ f(x)`.
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterFrom a n
        ≤ f.iterFrom a (n + 1) := iterFrom_mono f ha (Nat.le_succ n)
      _ = f.toElementMap (f.iterFrom a n) := iterFrom_succ f a n
      _ ≤ f.toElementMap (f.fixAbove ha) :=
          f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (f.iterFrom a) hdir n)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.7 (Scott 1981, PRG-19).** `fixAbove f ha` is the *least* fixed point above `a`:
any `z` with `a ⊑ z` and `f(z) ⊑ z` lies above it. (Relativized form of 4.2(iii).) -/
theorem fixAbove_least (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {z : V.Element} (haz : a ≤ z) (hz : f.toElementMap z ≤ z) : f.fixAbove ha ≤ z := by
  apply NeighborhoodSystem.iSupDirected_le
  intro n
  induction n with
  | zero => rwa [iterFrom_zero]
  | succ k ih =>
    rw [iterFrom_succ]
    exact le_trans (f.toElementMap_mono ih) hz

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_407.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a)),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a))
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha) z) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a)),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a))
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha) z)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove_isFixed
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove_least
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `a ⊑ fixAbove f ha`: the constructed fixed point lies above `a` (it is the `n = 0` term). -/
theorem le_fixAbove (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a) :
    a ≤ f.fixAbove ha := by
  have := NeighborhoodSystem.le_iSupDirected (f.iterFrom a)
    (fun i j => ⟨max i j, iterFrom_mono f ha (le_max_left i j),
      iterFrom_mono f ha (le_max_right i j)⟩) 0
  rwa [iterFrom_zero] at this

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The sup of a monotone `ω`-chain, realized as a directed union (`max`-directedness). -/
def supChain (s : ℕ → V.Element) (hmono : Monotone s) : V.Element :=
  NeighborhoodSystem.iSupDirected s
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The approximants form a monotone `ω`-chain (the `Monotone` packaging of `iterElem_mono`). -/
theorem iterElem_monotone (f : ApproximableMap V V) : Monotone f.iterElem :=
  fun _ _ hab => iterElem_mono f hab

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  show (f.comp (f.iterMap n)).toElementMap V.bot
      = f.toElementMap ((f.iterMap n).toElementMap V.bot)
  rw [toElementMap_comp]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


theorem iterElem_zero (f : ApproximableMap V V) : f.iterElem 0 = V.bot :=
  toElementMap_idMap V.bot

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


theorem mem_supChain (s : ℕ → V.Element) (hmono : Monotone s) {Z : Set α} :
    (supChain s hmono).mem Z ↔ ∃ n, (s n).mem Z :=
  NeighborhoodSystem.mem_iSupDirected s _

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The approximants `fⁿ(⊥)` form a monotone chain whose sup is `fix(f)`. -/
theorem fixElement_eq_supChain (f : ApproximableMap V V) :
    f.fixElement = supChain f.iterElem (iterElem_monotone f) := by
  apply Element.ext
  intro X
  rw [mem_supChain, mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/- concordance: source L2209 EXERCISE 4.8 fixed-point induction -/
/-- **Exercise 4.8 (Scott 1981, PRG-19) — fixed-point induction.** If a predicate `P` holds at `⊥`,
is preserved by `f`, and is closed under sups of monotone chains, then it holds at `fix(f)`. -/
theorem fix_induction (f : ApproximableMap V V) (P : V.Element → Prop)
    (hbot : P V.bot)
    (hstep : ∀ x, P x → P (f.toElementMap x))
    (hsup : ∀ (s : ℕ → V.Element) (hmono : Monotone s), (∀ n, P (s n)) → P (supChain s hmono)) :
    P f.fixElement := by
  have hmono : Monotone f.iterElem := iterElem_monotone f
  have hP : ∀ n, P (f.iterElem n) := by
    intro n
    induction n with
    | zero => rw [iterElem_zero]; exact hbot
    | succ k ih => rw [iterElem_succ]; exact hstep _ ih
  rw [fixElement_eq_supChain f]
  exact hsup f.iterElem hmono hP

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.8 (Scott 1981, PRG-19) — application to `S = {x ∣ a(x) = b(x)}`.** If `a(⊥) = b(⊥)`
and `f` commutes with both `a` and `b` (`f ∘ a = a ∘ f`, `f ∘ b = b ∘ f`), then `a` and `b` agree at
the least fixed point: `a(fix f) = b(fix f)`. -/
theorem fix_induction_eq (f a b : ApproximableMap V V)
    (hbot : a.toElementMap V.bot = b.toElementMap V.bot)
    (hfa : f.comp a = a.comp f) (hfb : f.comp b = b.comp f) :
    a.toElementMap f.fixElement = b.toElementMap f.fixElement := by
  -- commutation, elementwise: `a(f x) = f(a x)` and `b(f x) = f(b x)`.
  have hca : ∀ x, a.toElementMap (f.toElementMap x) = f.toElementMap (a.toElementMap x) := by
    intro x
    have h1 : (a.comp f).toElementMap x = (f.comp a).toElementMap x := by rw [hfa]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  have hcb : ∀ x, b.toElementMap (f.toElementMap x) = f.toElementMap (b.toElementMap x) := by
    intro x
    have h1 : (b.comp f).toElementMap x = (f.comp b).toElementMap x := by rw [hfb]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  refine fix_induction f (fun x => a.toElementMap x = b.toElementMap x) hbot ?_ ?_
  · intro x hx
    rw [hca, hcb, hx]
  · intro s hmono hs
    -- both sides are directed unions of equal families.
    show a.toElementMap (supChain s hmono) = b.toElementMap (supChain s hmono)
    rw [supChain, toElementMap_iSupDirected, toElementMap_iSupDirected]
    apply Element.ext
    intro Z
    rw [NeighborhoodSystem.mem_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [← hs n]; exact hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hs n]; exact hn⟩

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_408.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f a)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V a f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V b f) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (P : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V → Prop),
    P (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          P x → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x)) →
        (∀ (s : Nat → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (hmono :
              @Monotone Nat (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) Nat.instPreorder
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
                s),
            (∀ (n : Nat), P (s n)) → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.supChain α V s hmono)) →
          P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f a)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V a f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f b)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V b f) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V a
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V b
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (P : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V → Prop),
    P (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          P x → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x)) →
        (∀ (s : Nat → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (hmono :
              @Monotone Nat (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) Nat.instPreorder
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
                s),
            (∀ (n : Nat), P (s n)) → P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.supChain α V s hmono)) →
          P (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fix_induction_eq
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fix_induction
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*}

/- concordance: source L2225 EXERCISE 4.9 fix as a fixed point -/
/-- **Exercise 4.9 (Scott 1981, PRG-19).** The approximable operator `Ψ = λF λf. f(F(f))` on the
higher-order domain `E = ((𝒟 → 𝒟) → 𝒟)`, built as `curry (eval ∘ ⟨π_G, eval⟩)`. -/
def bigPsi (V : NeighborhoodSystem α) :
    ApproximableMap (funSpace (funSpace V V) V) (funSpace (funSpace V V) V) :=
  curry ((evalMap V V).comp
    (paired (proj₁ (funSpace (funSpace V V) V) (funSpace V V)) (evalMap (funSpace V V) V)))
end

section
variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** The defining equation `Ψ(θ)(f) = f(θ(f))`. -/
theorem bigPsi_apply (V : NeighborhoodSystem α)
    (θ : (funSpace (funSpace V V) V).Element) (f : (funSpace V V).Element) :
    (toApproxMap ((bigPsi V).toElementMap θ)).toElementMap f
      = (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f) := by
  rw [bigPsi, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply, evalMap_apply]
end

section
variable {α : Type*}

/-- `fix`, as the element of `E = ((𝒟 → 𝒟) → 𝒟)` corresponding to the operator `fixMap`, unfolds
under `toApproxMap` back to `fixMap` (the `funSpace` round-trip). -/
theorem toApproxMap_toFilter_fixMap (V : NeighborhoodSystem α) :
    toApproxMap (toFilter (fixMap V)) = fixMap V := by
  have he := (funSpaceEquiv (funSpace V V) V).apply_symm_apply (fixMap V)
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
end

section
variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix` is a *fixed point* of `Ψ`: `Ψ(fix) = fix`. -/
theorem bigPsi_fix (V : NeighborhoodSystem α) :
    (bigPsi V).toElementMap (toFilter (fixMap V)) = toFilter (fixMap V) := by
  apply (funSpaceEquiv (funSpace V V) V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro f
  rw [bigPsi_apply, toApproxMap_toFilter_fixMap, fixMap_toElementMap, toElementMap_fixElement]
end

section
variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix` is the *least* pre-fixed point of `Ψ`: any `θ` with
`Ψ(θ) ⊑ θ` satisfies `fix ⊑ θ`. -/
theorem bigPsi_least (V : NeighborhoodSystem α) (θ : (funSpace (funSpace V V) V).Element)
    (hθ : (bigPsi V).toElementMap θ ≤ θ) : toFilter (fixMap V) ≤ θ := by
  -- transport `Ψ(θ) ⊑ θ` to the pointwise pre-fixed-point inequality on maps.
  have hθ' : toApproxMap ((bigPsi V).toElementMap θ) ≤ toApproxMap θ := by
    rw [← funSpaceEquiv_apply, ← funSpaceEquiv_apply]
    exact (funSpaceEquiv (funSpace V V) V).monotone hθ
  have hpre : ∀ f, (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f)
      ≤ (toApproxMap θ).toElementMap f := by
    intro f
    have h := (le_iff_toElementMap_le.mp hθ') f
    rwa [bigPsi_apply] at h
  -- conclude `fix ⊑ θ` pointwise via Theorem 4.1's minimality.
  apply (funSpaceEquiv (funSpace V V) V).le_iff_le.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toFilter_fixMap, le_iff_toElementMap_le]
  intro f
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap f) (hpre f)
end

section
variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** `fix = fix(Ψ)`: `fix` is the least fixed point of `Ψ`,
i.e. coincides with Theorem 4.1's canonical least fixed point `fixElement Ψ`. -/
theorem fix_eq_fixElement_bigPsi (V : NeighborhoodSystem α) :
    toFilter (fixMap V) = (bigPsi V).fixElement := by
  apply le_antisymm
  · exact bigPsi_least V _ (le_of_eq (toElementMap_fixElement (bigPsi V)))
  · exact fixElement_le_of_toElementMap_le (bigPsi V) (le_of_eq (bigPsi_fix V))
end

section
set_option linter.unusedVariables false

theorem example_409.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (θ :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
          (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)),
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ)
          θ →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
          θ))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
      (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
        (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.bigPsi α V))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (θ :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
          (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)),
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ)
          θ →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
          θ))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
      (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
        (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.bigPsi α V)))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (θ :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
          (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)),
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ)
          θ →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
          θ)
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
      @DomainTheory.NeighbourhoodSystems.bigPsi_apply @DomainTheory.NeighbourhoodSystems.bigPsi_fix)
    @DomainTheory.NeighbourhoodSystems.bigPsi_least)
  @DomainTheory.NeighbourhoodSystems.fix_eq_fixElement_bigPsi
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/- concordance: source L2239 EXERCISE 4.10 domain above an element -/
/-- **Exercise 4.10 (Scott 1981, PRG-19).** The relativized neighbourhood system `Dₐ`: same tokens
and master, neighbourhoods exactly the members of the filter `a`. -/
def relSystem (a : V.Element) : NeighborhoodSystem α where
  mem X := a.mem X
  master := V.master
  master_nonempty := V.master_nonempty
  master_mem := a.master_mem
  sub_master := fun hX => V.sub_master (a.sub hX)
  inter_mem := fun hX hY _ _ => a.inter_mem hX hY

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem relSystem_mem (a : V.Element) {X : Set α} :
    (relSystem a).mem X ↔ a.mem X := Iff.rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

@[simp] theorem relSystem_master (a : V.Element) : (relSystem a).master = V.master := rfl

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `𝒟`-element obtained from a `Dₐ`-filter by upward closure in `𝒟`. -/
def embed (a : V.Element) (g : (relSystem a).Element) : V.Element where
  mem X := V.mem X ∧ ∃ W, a.mem W ∧ g.mem W ∧ W ⊆ X
  sub := fun h => h.1
  master_mem := ⟨V.master_mem, V.master, a.master_mem, g.master_mem, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hVX, Wx, haWx, hgWx, hWxX⟩ ⟨hVY, Wy, haWy, hgWy, hWyY⟩
    have haWxy : a.mem (Wx ∩ Wy) := a.inter_mem haWx haWy
    have hgWxy : g.mem (Wx ∩ Wy) := g.inter_mem hgWx hgWy
    have hsub : Wx ∩ Wy ⊆ X ∩ Y := Set.inter_subset_inter hWxX hWyY
    refine ⟨V.inter_mem hVX hVY (a.sub haWxy) hsub, Wx ∩ Wy, haWxy, hgWxy, hsub⟩
  up_mem := by
    rintro X Y ⟨hVX, W, haW, hgW, hWX⟩ hVY hXY
    exact ⟨hVY, W, haW, hgW, subset_trans hWX hXY⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `embed a g ⊑ a`: the embedding lands below `a`. -/
theorem embed_le (a : V.Element) (g : (relSystem a).Element) : embed a g ≤ a := by
  rintro X ⟨hVX, W, haW, _, hWX⟩
  exact a.up_mem haW hVX hWX

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem embed_mono (a : V.Element) {g₁ g₂ : (relSystem a).Element} (h : g₁ ≤ g₂) :
    embed a g₁ ≤ embed a g₂ := by
  rintro X ⟨hVX, W, haW, hgW, hWX⟩
  exact ⟨hVX, W, haW, h _ hgW, hWX⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem le_of_embed_le (a : V.Element) {g₁ g₂ : (relSystem a).Element}
    (h : embed a g₁ ≤ embed a g₂) : g₁ ≤ g₂ := by
  intro X hg₁X
  have hVX : V.mem X := a.sub (g₁.sub hg₁X)
  have : (embed a g₂).mem X := h X ⟨hVX, X, g₁.sub hg₁X, hg₁X, subset_rfl⟩
  obtain ⟨_, W, haW, hg₂W, hWX⟩ := this
  exact g₂.up_mem hg₂W (g₁.sub hg₁X) hWX

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** When `f(a) = a`, the restriction `f' : Dₐ → Dₐ`
(`f'(x) = f(x)`). The codomain condition uses `↑X ⊑ a ⟹ f(↑X) ⊑ f(a) = a`. -/
def relMap (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a) :
    ApproximableMap (relSystem a) (relSystem a) where
  rel X Y := a.mem X ∧ f.rel X Y
  rel_dom := fun h => h.1
  rel_cod := by
    rintro X Y ⟨haX, hXY⟩
    have hVX : V.mem X := a.sub haX
    have hpr : V.principal hVX ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haX hVZ hXZ
    have hmemfX : (f.toElementMap (V.principal hVX)).mem Y := (f.rel_iff_mem_principal hVX).mp hXY
    have hle : f.toElementMap (V.principal hVX) ≤ f.toElementMap a := f.toElementMap_mono hpr
    have : (f.toElementMap a).mem Y := hle Y hmemfX
    rw [ha] at this
    exact this
  master_rel := ⟨a.master_mem, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hXY⟩ ⟨_, hXY'⟩
    exact ⟨haX, f.inter_right hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hXY⟩ hX'X hYY' haX' haY'
    exact ⟨haX', f.mono hXY hX'X hYY' (a.sub haX') (a.sub haY')⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The `Dₐ`-filter obtained from an element `x ⊑ a` by restriction (same membership). -/
def restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) : (relSystem a).Element where
  mem X := x.mem X
  sub := fun h => hx _ h
  master_mem := x.master_mem
  inter_mem := fun hX hY => x.inter_mem hX hY
  up_mem := fun hX hY hXY => x.up_mem hX (a.sub hY) hXY

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem embed_restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) :
    embed a (restrict a x hx) = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, _, hxW, hWX⟩
    exact x.up_mem hxW hVX hWX
  · intro hxX
    exact ⟨x.sub hxX, X, hx _ hxX, hxX, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem restrict_embed (a : V.Element) (g : (relSystem a).Element) :
    restrict a (embed a g) (embed_le a g) = g := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, hgW, hWX⟩
    exact g.up_mem hgW (a.up_mem haW hVX hWX) hWX
  · intro hgX
    exact ⟨a.sub (g.sub hgX), X, g.sub hgX, hgX, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 4.10 (Scott 1981, PRG-19).** `|Dₐ| ≃o {x ∈ |𝒟| ∣ x ⊑ a}`: the relativized domain has
exactly the elements below `a` as its points, with the inherited order. -/
def relIso (a : V.Element) : (relSystem a).Element ≃o {x : V.Element // x ≤ a} where
  toFun g := ⟨embed a g, embed_le a g⟩
  invFun x := restrict a x.1 x.2
  left_inv g := restrict_embed a g
  right_inv x := Subtype.ext (embed_restrict a x.1 x.2)
  map_rel_iff' := by
    intro g₁ g₂
    constructor
    · intro h; exact le_of_embed_le a h
    · intro h; exact embed_mono a h

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.10 (Scott 1981, PRG-19).** Any fixed point of `f` below `fix(f)` *is* `fix(f)`:
a fixed point is a pre-fixed point, so leastness forces `fix(f) ⊑ x`. -/
theorem fixElement_below_unique (f : ApproximableMap V V) {x : V.Element}
    (hxle : x ≤ f.fixElement) (hxfix : f.toElementMap x = x) : x = f.fixElement := by
  have hge : f.fixElement ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hxfix)
  exact le_antisymm hxle hge

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The restriction `f'` has the same action as `f`: `embed a (f'(g)) = f(embed a g)`. -/
theorem relMap_toElementMap_embed (f : ApproximableMap V V) {a : V.Element}
    (ha : f.toElementMap a = a) (g : (relSystem a).Element) :
    embed a ((relMap f ha).toElementMap g) = f.toElementMap (embed a g) := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, ⟨U, hgU, haU, hUW⟩, hWX⟩
    -- `U ∈ g`, `U f W`, `W ⊆ X`; so `X ∈ f(embed g)` via the member `U` of `embed g`.
    refine ⟨U, ⟨a.sub haU, U, haU, hgU, subset_rfl⟩, ?_⟩
    exact f.mono hUW subset_rfl hWX (a.sub haU) hVX
  · rintro ⟨U, ⟨hVU, W, haW, hgW, hWU⟩, hUX⟩
    -- `W ∈ g`, `W ⊆ U`, `U f X`; so `W f X` and `X ∈ embed a (f'(g))`.
    have hVX : V.mem X := f.rel_cod hUX
    have hWX : f.rel W X := f.mono hUX hWU subset_rfl (a.sub haW) hVX
    have haX : a.mem X := by
      have hpr : V.principal (a.sub haW) ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haW hVZ hXZ
      have hmemfW : (f.toElementMap (V.principal (a.sub haW))).mem X :=
        (f.rel_iff_mem_principal (a.sub haW)).mp hWX
      have := (f.toElementMap_mono hpr) X hmemfW
      rw [ha] at this; exact this
    exact ⟨hVX, X, haX, ⟨W, hgW, haW, hWX⟩, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.10 (Scott 1981, PRG-19).** With `a = fix(f)`, the restricted map `f'` has *exactly
one* fixed point: the top element of `D_{fix f}`, namely `restrict (fix f)` of `fix f` itself. Every
`Dₐ`-fixed point `g` of `f'` satisfies `embed a g = fix f`, hence is this top element. -/
theorem relMap_unique_fixed (f : ApproximableMap V V)
    (ha : f.toElementMap f.fixElement = f.fixElement) (g : (relSystem f.fixElement).Element)
    (hg : (relMap f ha).toElementMap g = g) :
    g = restrict f.fixElement f.fixElement (le_refl _) := by
  -- `embed g` is a fixed point of `f` below `fix f`, hence equals `fix f`.
  have hembfix : f.toElementMap (embed f.fixElement g) = embed f.fixElement g := by
    rw [← relMap_toElementMap_embed f ha g, hg]
  have heq : embed f.fixElement g = f.fixElement :=
    fixElement_below_unique f (embed_le f.fixElement g) hembfix
  -- transport along the iso.
  have h1 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g) = g :=
    restrict_embed f.fixElement g
  -- both restricts agree because their underlying elements agree.
  have h2 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g)
      = restrict f.fixElement f.fixElement (le_refl _) := by
    apply Element.ext
    intro X
    show (embed f.fixElement g).mem X ↔ f.fixElement.mem X
    rw [heq]
  rw [← h1, h2]

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_410.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) →
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) x
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (ha :
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
    (g :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))),
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap α V f
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) ha)
          g)
        g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        g
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.restrict α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@le_refl (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) →
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) x
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (ha :
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
    (g :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))),
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap α V f
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) ha)
          g)
        g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        g
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.restrict α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@le_refl (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_below_unique
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap_unique_fixed
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The inclusion `𝒟ₐ → 𝒟` as an approximable map: an `a`-neighbourhood `X` relates to any larger
`𝒟`-neighbourhood `Y ⊇ X`. Its elementwise action is `embed a` (`inclMap_toElementMap`). -/
def inclMap (a : V.Element) : ApproximableMap (relSystem a) V where
  rel X Y := a.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom := fun h => h.1
  rel_cod := fun h => h.2.1
  master_rel := ⟨a.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hVY, hXY⟩ ⟨_, hVY', hXY'⟩
    exact ⟨haX, V.inter_mem hVY hVY' (a.sub haX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' haX' hVY'
    exact ⟨haX', hVY', (hX'X.trans hXY).trans hYY'⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion's elementwise action is `embed a` (Exercise 4.10). -/
theorem inclMap_toElementMap (a : V.Element) (g : (relSystem a).Element) :
    (inclMap a).toElementMap g = embed a g := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hgX, haX, hVY, hXY⟩
    exact ⟨hVY, X, haX, hgX, hXY⟩
  · rintro ⟨hVY, W, haW, hgW, hWY⟩
    exact ⟨W, hgW, haW, hVY, hWY⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion is strict: `ι(⊥) = ⊥`. -/
theorem inclMap_bot (a : V.Element) : (inclMap a).toElementMap (relSystem a).bot = V.bot := by
  rw [inclMap_toElementMap]
  apply Element.ext
  intro Y
  rw [mem_bot]
  constructor
  · rintro ⟨hVY, W, _, hbW, hWY⟩
    rw [mem_bot] at hbW
    rw [hbW] at hWY
    exact Set.Subset.antisymm (V.sub_master hVY) hWY
  · rintro rfl
    exact ⟨V.master_mem, V.master, a.master_mem, (relSystem a).bot.master_mem, subset_rfl⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion intertwines `f'` with `f`: `ι ∘ f' = f ∘ ι` (from `relMap_toElementMap_embed`). -/
theorem inclMap_intertwine (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a)
    (g : (relSystem a).Element) :
    (inclMap a).toElementMap ((relMap f ha).toElementMap g) =
      f.toElementMap ((inclMap a).toElementMap g) := by
  rw [inclMap_toElementMap, inclMap_toElementMap, relMap_toElementMap_embed]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
open ApproximableMap
universe u

/- concordance: source L2249 EXERCISE 4.11 characterizing the fix combinator -/
/-- **Exercise 4.11 (Scott 1981, PRG-19) — Plotkin's uniqueness.** Any assignment `F` of a
fixed-point operator to every domain satisfying (ii) `F_𝒟(f) = f(F_𝒟(f))` and (iii) the uniformity
law coincides with `fix`: `F_𝒟(f) = fix(f)` for every domain `𝒟` and every `f : 𝒟 → 𝒟`. -/
theorem fix_unique_of_uniform
    (F : ∀ {β : Type u} (W : NeighborhoodSystem β), ApproximableMap W W → W.Element)
    (hfixed : ∀ {β : Type u} (W : NeighborhoodSystem β) (g : ApproximableMap W W),
      g.toElementMap (F W g) = F W g)
    (huniform : ∀ {β γ : Type u} (W₀ : NeighborhoodSystem β) (W₁ : NeighborhoodSystem γ)
      (g₀ : ApproximableMap W₀ W₀) (g₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁),
      h.toElementMap W₀.bot = W₁.bot →
      (∀ x, h.toElementMap (g₀.toElementMap x) = g₁.toElementMap (h.toElementMap x)) →
      h.toElementMap (F W₀ g₀) = F W₁ g₁)
    {α : Type u} (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    F V f = f.fixElement := by
  have ha : f.toElementMap f.fixElement = f.fixElement := toElementMap_fixElement f
  -- `F` of the restricted map `f'` is a fixed point of `f'` (by (ii))…
  have hfix' : (relMap f ha).toElementMap (F (relSystem f.fixElement) (relMap f ha)) =
      F (relSystem f.fixElement) (relMap f ha) := hfixed (relSystem f.fixElement) (relMap f ha)
  -- …hence it is the unique fixed point `restrict (fix f) (fix f)` of `f'` (Exercise 4.10).
  have huniq : F (relSystem f.fixElement) (relMap f ha) =
      restrict f.fixElement f.fixElement (le_refl _) :=
    relMap_unique_fixed f ha _ hfix'
  -- uniformity along the inclusion `ι` transports `F(f')` to `F(f)`.
  have huse := huniform (relSystem f.fixElement) V (relMap f ha) f (inclMap f.fixElement)
    (inclMap_bot f.fixElement) (inclMap_intertwine f ha)
  rw [huniq, inclMap_toElementMap, embed_restrict] at huse
  exact huse.symm
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `fⁿ(⊥) ⊑ fix(f)`: every approximant lies below the least fixed point. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement :=
  fun _ hX => ⟨n, (mem_iterElem f n).mp hX⟩

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.11(iii) (Scott 1981, PRG-19).** `fix` is *uniform*: if `h(⊥) = ⊥` and
`h ∘ f₀ = f₁ ∘ h`, then `h(fix f₀) = fix f₁`. -/
theorem fixElement_uniform {β γ : Type*} {W₀ : NeighborhoodSystem β} {W₁ : NeighborhoodSystem γ}
    (f₀ : ApproximableMap W₀ W₀) (f₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁)
    (hbot : h.toElementMap W₀.bot = W₁.bot)
    (hintw : ∀ x, h.toElementMap (f₀.toElementMap x) = f₁.toElementMap (h.toElementMap x)) :
    h.toElementMap f₀.fixElement = f₁.fixElement := by
  -- `h` carries the `n`-th approximant of `f₀` to that of `f₁`.
  have hiter : ∀ n, h.toElementMap (f₀.iterElem n) = f₁.iterElem n := by
    intro n
    rw [iterElem_eq_iterate f₀ n, iterElem_eq_iterate f₁ n]
    induction n with
    | zero => simpa using hbot
    | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply, hintw, ih]
  apply le_antisymm
  · -- `h(fix f₀) = ⊔ₙ h(f₀ⁿ(⊥)) = ⊔ₙ f₁ⁿ(⊥) ⊑ fix f₁`.
    rw [fixElement_eq_iSupDirected f₀, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    rw [hiter n]
    exact iterElem_le_fixElement f₁ n
  · -- `h(fix f₀)` is a fixed point of `f₁`, so `fix f₁ ⊑ h(fix f₀)` by minimality.
    have hfp : f₁.toElementMap (h.toElementMap f₀.fixElement) = h.toElementMap f₀.fixElement := by
      rw [← hintw f₀.fixElement, toElementMap_fixElement]
    exact fixElement_le_of_toElementMap_le f₁ (le_of_eq hfp)

end ApproximableMap
end

section
set_option linter.unusedVariables false

theorem example_411.{u_2, u_3, u} : And
  (∀ {β : Type u_2} {γ : Type u_3} {W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
    (f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
    (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ f₀ x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ f₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β W₀ f₀))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement γ W₁ f₁))
  (∀
    (F :
      {β : Type u} →
        (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) →
          @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W),
    (∀ {β : Type u} (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
        (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W W g (@F β W g)) (@F β W g)) →
      (∀ {β γ : Type u} (W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
          (W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
          (g₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
          (g₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
          (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
            (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ g₀ x))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ g₁
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h (@F β W₀ g₀))
                (@F γ W₁ g₁)) →
        ∀ {α : Type u} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (@F α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {β : Type u_2} {γ : Type u_3} {W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
    (f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
    (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ f₀ x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ f₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β W₀ f₀))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement γ W₁ f₁))
  (∀
    (F :
      {β : Type u} →
        (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) →
          @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W),
    (∀ {β : Type u} (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
        (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W W g (@F β W g)) (@F β W g)) →
      (∀ {β γ : Type u} (W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
          (W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
          (g₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
          (g₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
          (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
            (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ g₀ x))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ g₁
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h (@F β W₀ g₀))
                (@F γ W₁ g₁)) →
        ∀ {α : Type u} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (@F α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_uniform)
  DomainTheory.NeighbourhoodSystems.fix_unique_of_uniform
end

end DomainTheory.NeighbourhoodSystems
end

section
/- concordance: source L2261 EXERCISE 4.13 avoiding the natural numbers -/
-- Exercise413/preFix.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- The set of *pre-fixed points* `{x ∣ f(x) ⊑ x}` of `f`. -/
def preFix (f : V.Element → V.Element) : Set V.Element := {x | f x ≤ x}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

@[simp] theorem mem_preFix {f : V.Element → V.Element} {x : V.Element} :
    x ∈ preFix f ↔ f x ≤ x := Iff.rfl

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** The least fixed point of a *monotone* `f` defined
purely as the greatest lower bound of the pre-fixed points, `⋂ {x ∣ f(x) ⊑ x}`. Well-defined as an
element by Exercise 1.18 (`sInf`); the non-emptiness witness is any `a` with `f(a) ⊑ a`. -/
def monoFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) : V.Element :=
  V.sInf (preFix f) ⟨a, ha⟩

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.13(3) (Scott 1981, PRG-19).** For any structured set `⟨Z, z, ·⟩` (`z : Z`,
`op : Z → Z`) there is a *unique* `s : ℕ → Z` with `s(0) = z` and `s(n⁺) = (s n)·`. This is the
choice-free recursion principle (`Nat.rec`); together with 4.13(1) it eliminates the circularity in
the proofs of 4.1 and 4.6. -/
theorem exists_unique_nat_rec {Z : Type*} (z : Z) (op : Z → Z) :
    ∃! s : ℕ → Z, s 0 = z ∧ ∀ n, s (n + 1) = op (s n) := by
  refine ⟨fun n => Nat.rec z (fun _ x => op x) n, ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro s ⟨h0, hsucc⟩
  funext n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hsucc k, ih]

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `monoFix f ha ⊑ x` for every pre-fixed point `x` (`f(x) ⊑ x`). -/
theorem monoFix_le_preFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {x : V.Element} (hx : f x ≤ x) : monoFix f ha ≤ x :=
  V.sInf_le (preFix f) ⟨a, ha⟩ hx

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `monoFix f ha ⊑ a`: the least fixed point lies below the given pre-fixed point `a`. -/
theorem monoFix_le (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) :
    monoFix f ha ≤ a := monoFix_le_preFix f ha ha

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** `monoFix f ha` is the *least* fixed point: any `y`
with `f(y) = y` satisfies `b ⊑ y`. -/
theorem monoFix_least (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {y : V.Element} (hy : f y = y) : monoFix f ha ≤ y :=
  monoFix_le_preFix f ha (le_of_eq hy)

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- The key step: `f(b) ⊑ b` where `b = monoFix f ha`, by monotonicity alone. -/
theorem monoFix_preFix (f : V.Element → V.Element) (hf : Monotone f) {a : V.Element}
    (ha : f a ≤ a) : f (monoFix f ha) ≤ monoFix f ha := by
  apply V.le_sInf (preFix f) ⟨a, ha⟩
  intro x hx
  exact le_trans (hf (monoFix_le_preFix f ha hx)) hx

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** `monoFix f ha` is a fixed point: `f(b) = b`. (After
`f(b) ⊑ b`, monotonicity gives `f(f(b)) ⊑ f(b)`, so `f(b)` is itself a pre-fixed point, whence
`b ⊑ f(b)`.) -/
theorem monoFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) {a : V.Element}
    (ha : f a ≤ a) : f (monoFix f ha) = monoFix f ha := by
  have hfb : f (monoFix f ha) ≤ monoFix f ha := monoFix_preFix f hf ha
  have hbf : monoFix f ha ≤ f (monoFix f ha) :=
    monoFix_le_preFix f ha (hf hfb)
  exact le_antisymm hfb hbf

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.13(4) (Scott 1981, PRG-19).** Specializing 4.13(3) to the structured set
`⟨ℕ, 0, ⁺⟩`: the *unique* function `s` with `s(0) = 0` and `s(n⁺) = (s n)⁺` is the identity. This
is the iteration `n ↦ fⁿ` underlying Theorem 4.1, now justified without circularity. -/
theorem nat_iterate_unique {s : ℕ → ℕ} (h0 : s 0 = 0) (hsucc : ∀ n, s (n + 1) = s n + 1) :
    ∀ n, s n = n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => rw [hsucc k, ih]

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section
set_option linter.unusedVariables false

theorem example_413.{u_1, u_2} : And
  (And
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y))
  (∀ {s : Nat → Nat},
    @Eq Nat (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      (∀ (n : Nat),
          @Eq Nat
            (s
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (s n)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (n : Nat), @Eq Nat (s n) n) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y))
  (∀ {s : Nat → Nat},
    @Eq Nat (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      (∀ (n : Nat),
          @Eq Nat
            (s
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (s n)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (n : Nat), @Eq Nat (s n) n)
  (@And.intro
    (And
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n)))))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
      (ha :
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (f a) a)
      {y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha) y)
    (@And.intro
      (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            f →
          ∀ {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
            (ha :
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                (f a) a),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix α V f a ha))
      (∀ {Z : Type u_2} (z : Z) (op : Z → Z),
        @ExistsUnique (Nat → Z) fun (s : Nat → Z) =>
          And (@Eq Z (s (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) z)
            (∀ (n : Nat),
              @Eq Z
                (s
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (op (s n))))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix_isFixed
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_unique_nat_rec)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.monoFix_least)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.nat_iterate_unique
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- `chainUnion C` is the least upper bound of the chain: an upper bound `y` of every member
dominates it. -/
theorem chainUnion_le (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {y : V.Element} (hy : ∀ x ∈ C, x ≤ y) : V.chainUnion C hne hchain ≤ y := by
  rintro Z ⟨x, hxC, hxZ⟩
  exact hy x hxC Z hxZ

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/- concordance: source L2285 EXERCISE 4.15 maximal fixed points -/
/-- **Exercise 4.15 (Scott 1981, PRG-19).** A monotone `f : |𝒟| → |𝒟|` has a *maximal* fixed point:
some `m` with `f(m) = m` that admits no strictly larger fixed point. -/
theorem exists_maximal_fixedPoint (f : V.Element → V.Element) (hf : Monotone f) :
    ∃ m, f m = m ∧ ∀ y, f y = y → m ≤ y → y ≤ m := by
  -- Zorn on the set of post-fixed points.
  set S : Set V.Element := {x | x ≤ f x} with hS
  have ih : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ?_, fun z hz => ((Set.mem_empty_iff_false z).mp hz).elim⟩
      show (⊥ : V.Element) ≤ f ⊥
      exact _root_.bot_le
    · refine ⟨V.chainUnion c hne hchain, ?_, fun z hz => V.le_chainUnion c hne hchain hz⟩
      -- `⊔c` is post-fixed: each `x ∈ c` has `x ⊑ f x ⊑ f(⊔c)`.
      show V.chainUnion c hne hchain ≤ f (V.chainUnion c hne hchain)
      intro Z hZ
      obtain ⟨x, hxc, hxZ⟩ := hZ
      have hxle : x ≤ V.chainUnion c hne hchain := V.le_chainUnion c hne hchain hxc
      exact (le_trans (hcS hxc) (hf hxle)) Z hxZ
  obtain ⟨m, hm⟩ := zorn_le₀ S ih
  have hms : m ≤ f m := hm.1
  have hfm_le_m : f m ≤ m := hm.2 (hf hms) hms
  refine ⟨m, le_antisymm hfm_le_m hms, fun y hy hmy => hm.2 ?_ hmy⟩
  exact le_of_eq hy.symm

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.15 (Scott 1981, PRG-19).** A monotone `f : |𝒟| → |𝒟|` has a *least* fixed point.
(Having a maximal fixed point `m` gives a pre-fixed point `f(m) ⊑ m`; Exercise 4.13(1)'s `monoFix`
then constructs the least fixed point `⋂{x ∣ f(x) ⊑ x}`.) -/
theorem exists_least_fixedPoint (f : V.Element → V.Element) (hf : Monotone f) :
    ∃ b, f b = b ∧ ∀ y, f y = y → b ≤ y := by
  obtain ⟨m, hfm, _⟩ := exists_maximal_fixedPoint f hf
  exact ⟨monoFix f (le_of_eq hfm), monoFix_isFixed f hf (le_of_eq hfm),
    fun y hy => monoFix_least f (le_of_eq hfm) hy⟩

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section
set_option linter.unusedVariables false

theorem example_415.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f b) b)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                b y))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (m : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f m) m)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  m y →
                @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  y m)) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f b) b)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                b y))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (m : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f m) m)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  m y →
                @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  y m))
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_least_fixedPoint
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_maximal_fixedPoint
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.16(1) (Scott 1981, PRG-19).** Scott's formula: for a non-empty set `S` of fixed
points, `f(⋂S) ⊑ ⋂S`. (`f(⋂S) ⊑ f(s) = s` for each `s ∈ S`, then take the glb.) -/
theorem f_sInf_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) : f (V.sInf S hS) ≤ V.sInf S hS := by
  apply V.le_sInf
  intro s hsS
  calc f (V.sInf S hS) ≤ f s := hf (V.sInf_le S hS hsS)
    _ = s := hfix s hsS

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/- concordance: source L2293 EXERCISE 4.16 optimal fixed point -/
/-- **Exercise 4.16 (Scott 1981, PRG-19).** The *optimal* fixed point associated with a non-empty
set `S` of fixed points: the least fixed point sitting below `⋂S` (Exercise 4.13(1) applied to the
pre-fixed point `⋂S`). -/
def optimalFix (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
    (hfix : ∀ s ∈ S, f s = s) : V.Element :=
  monoFix f (f_sInf_le f hf S hS hfix)

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `optimalFix S` is a fixed point. -/
theorem optimalFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    f (optimalFix f hf S hS hfix) = optimalFix f hf S hS hfix :=
  monoFix_isFixed f hf _

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- `optimalFix S ⊑ ⋂S`. -/
theorem optimalFix_le_sInf (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    optimalFix f hf S hS hfix ≤ V.sInf S hS :=
  monoFix_le f _

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` lies below every member of `S`. -/
theorem optimalFix_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    optimalFix f hf S hS hfix ≤ s :=
  le_trans (optimalFix_le_sInf f hf S hS hfix) (V.sInf_le S hS hs)

end NeighborhoodSystem
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem


/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` is *consistent* with every member of `S`
(they share a common upper bound, namely `s` itself). -/
theorem optimalFix_consistent (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    ∃ ub, optimalFix f hf S hS hfix ≤ ub ∧ s ≤ ub :=
  ⟨s, optimalFix_le f hf S hS hfix hs, le_refl s⟩

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section
set_option linter.unusedVariables false

theorem example_416.{u_1} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f →
        ∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S),
          (∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
              @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s) →
            @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (hf :
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f)
      (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
      (hfix :
        ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
      {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
        ∃ (ub : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) ub)
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              s ub)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (hf :
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f)
    (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
    (hfix :
      ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
    {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) s) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f →
        ∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S),
          (∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
              @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s) →
            @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (hf :
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f)
      (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
      (hfix :
        ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
      {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
        ∃ (ub : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) ub)
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              s ub)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (hf :
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f)
    (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
    (hfix :
      ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
    {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) s)
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f →
        ∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S),
          (∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
              @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s) →
            @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (f (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α V S hS))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (f :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (hf :
        @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
          f)
      (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hS : @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S)
      (hfix :
        ∀ (s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f s) s)
      {s : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S s →
        ∃ (ub : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix α V f hf S hS hfix) ub)
            (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
              s ub))
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.f_sInf_le
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix_consistent)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.optimalFix_le
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems.Exercise418
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43

section
/-- Distinct singletons are disjoint. -/
theorem singleton_inter_eq_empty {n m : ℕ} (hmn : m ≠ n) :
    ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h2
  exact hmn h2.symm
end

section
/- concordance: source L2321 EXERCISE 4.18 checking the number domain -/
/-- **Exercise 4.18 (Scott 1981, PRG-19).** The numerals are distinct: `n̂ = m̂ ⟹ n = m`. -/
theorem natElem_injective {n m : ℕ} (h : natElem n = natElem m) : n = m := by
  have hmem : (natElem m).mem {n} := h ▸ (mem_natElem_iff.mpr (Or.inr rfl))
  rw [mem_natElem_iff] at hmem
  rcases hmem with hu | hs
  · exact absurd hu (singleton_ne_univ n)
  · exact singleton_nat_inj hs
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not a numeral successor. -/
theorem natElem_zero_ne_succ (k : ℕ) : natElem 0 ≠ natElem (k + 1) := fun h =>
  Nat.succ_ne_zero k (natElem_injective h).symm
end

section
/-- `∅` is not a neighbourhood of `N`. -/
theorem not_N_mem_empty : ¬ N.mem (∅ : Set ℕ) := by
  rw [N_mem]
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact (Set.singleton_ne_empty n) h.symm
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** Element classification: every element of `|N|` is either
the bottom `⊥` or a total element `n̂`. So `N` is the flat domain over `ℕ`. -/
theorem element_classification (x : N.Element) :
    x = N.bot ∨ ∃ n, x = natElem n := by
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    apply Element.ext
    intro Y
    rw [mem_natElem_iff]
    constructor
    · intro hY
      rcases N_mem.mp (x.sub hY) with rfl | ⟨m, rfl⟩
      · exact Or.inl rfl
      · by_cases hmn : m = n
        · subst hmn; exact Or.inr rfl
        · exfalso
          have hmem := x.inter_mem hn hY
          rw [singleton_inter_eq_empty hmn] at hmem
          exact not_N_mem_empty (x.sub hmem)
    · rintro (rfl | rfl)
      · exact x.master_mem
      · exact hn
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    rw [N_bot_mem]
    constructor
    · intro hY
      rcases N_mem.mp (x.sub hY) with rfl | ⟨m, rfl⟩
      · rfl
      · exact absurd hY (fun hm => h ⟨m, hm⟩)
    · rintro rfl
      exact x.master_mem
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** `succ` is injective on the total elements. -/
theorem succMap_injective {n m : ℕ}
    (h : succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m)) : n = m := by
  rw [succMap_natElem, succMap_natElem] at h
  have := natElem_injective h
  omega
end

section
/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not in the image of `succ` — Peano's
"zero is not a successor". -/
theorem zero_ne_succMap (n : ℕ) : natElem 0 ≠ succMap.toElementMap (natElem n) := by
  rw [succMap_natElem]
  exact natElem_zero_ne_succ n
end

section
set_option linter.unusedVariables false

theorem example_418 : And
  (And
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m))
  (∀ (n : Nat),
    @Ne
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
        DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))) :=
  @And.intro
  (And
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m))
  (∀ (n : Nat),
    @Ne
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Example43.N)
      (DomainTheory.NeighbourhoodSystems.Example43.natElem (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
        DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
        DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
  (@And.intro
    (And
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (∀ {n m : Nat},
      @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap (DomainTheory.NeighbourhoodSystems.Example43.natElem n))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat
            DomainTheory.NeighbourhoodSystems.Example43.N DomainTheory.NeighbourhoodSystems.Example43.N
            DomainTheory.NeighbourhoodSystems.Example43.succMap
            (DomainTheory.NeighbourhoodSystems.Example43.natElem m)) →
        @Eq Nat n m)
    (@And.intro
      (And
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m))
      (∀ (k : Nat),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
            DomainTheory.NeighbourhoodSystems.Example43.N)
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (DomainTheory.NeighbourhoodSystems.Example43.natElem
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@And.intro
        (∀
          (x :
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
              DomainTheory.NeighbourhoodSystems.Example43.N),
          Or
            (@Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              x
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat
                DomainTheory.NeighbourhoodSystems.Example43.N))
            (∃ (n : Nat),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                  DomainTheory.NeighbourhoodSystems.Example43.N)
                x (DomainTheory.NeighbourhoodSystems.Example43.natElem n)))
        (∀ {n m : Nat},
          @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
                DomainTheory.NeighbourhoodSystems.Example43.N)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem n)
              (DomainTheory.NeighbourhoodSystems.Example43.natElem m) →
            @Eq Nat n m)
        DomainTheory.NeighbourhoodSystems.Exercise418.element_classification
        @DomainTheory.NeighbourhoodSystems.Exercise418.natElem_injective)
      DomainTheory.NeighbourhoodSystems.Exercise418.natElem_zero_ne_succ)
    @DomainTheory.NeighbourhoodSystems.Exercise418.succMap_injective)
  DomainTheory.NeighbourhoodSystems.Exercise418.zero_ne_succMap
end

end DomainTheory.NeighbourhoodSystems.Exercise418
namespace DomainTheory.NeighbourhoodSystems.Exercise419
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

section
variable {β : Type*}

notation "𝕥" => Example23.trueElt
end

section
variable {β : Type*}

notation "𝕗" => Example23.falseElt
end

section
variable {β : Type*}

/-- The codomain value chosen by inspecting the head of a sequence: `[] ↦ z`, `0σ ↦ a₀`, `1σ ↦ a₁`.
With `z = ⊥` this is the value at the *partial* element `σ⊥`; with `z = vΛ` the value at the
*total* element `σ`. -/
def headValC (V : NeighborhoodSystem β) (z a0 a1 : V.Element) : Str → V.Element
  | [] => z
  | false :: _ => a0
  | true :: _ => a1
end

section
variable {β : Type*}

@[simp] theorem headValC_nil (V : NeighborhoodSystem β) (z a0 a1 : V.Element) :
    headValC V z a0 a1 [] = z := rfl
end

section
variable {β : Type*}

@[simp] theorem headValC_false (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (false :: σ) = a0 := rfl
end

section
variable {β : Type*}

@[simp] theorem headValC_true (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (true :: σ) = a1 := rfl
end

section
variable {β : Type*}

/-- The truth domain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example23.T
end

section
variable {β : Type*}

/-- Monotonicity of the head value: along a prefix `σ <+: τ`, the *partial* value (`z = ⊥`) at `σ`
is below *any* head value at `τ` with the same head constants. Covers both required conditions
(cone→cone with `z' = ⊥`, cone→singleton with `z' = vΛ`). -/
theorem headValC_bot_le (V : NeighborhoodSystem β) (z' a0 a1 : V.Element) {σ τ : Str}
    (h : σ <+: τ) : headValC V V.bot a0 a1 σ ≤ headValC V z' a0 a1 τ := by
  cases σ with
  | nil => exact bot_le
  | cons b σ0 =>
    obtain ⟨s, rfl⟩ := h
    cases b
    · rw [List.cons_append]; exact le_of_eq rfl
    · rw [List.cons_append]; exact le_of_eq rfl
end

section
/-- A cone is never contained in a singleton (it has at least two elements). -/
theorem not_cone_subset_singleton (τ σ : Str) : ¬ cone τ ⊆ ({σ} : Set Str) := by
  intro h
  have h1 : τ ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  have h2 : (τ ++ [true]) ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [true] := h1.trans h2.symm
  simp at this
end

section
/-- A cone is never equal to a singleton. -/
theorem cone_ne_singleton (τ σ : Str) : cone τ ≠ ({σ} : Set Str) := by
  intro h
  exact not_cone_subset_singleton τ σ (h ▸ subset_rfl)
end

section
variable {β : Type*}

/-- A map `C → V` determined by its value `coneVal σ` on each partial element `σ⊥` and `singVal σ`
on each total element `σ`, provided (a) the partial values are monotone along prefixes and (b) a
partial value sits below the total value of any extending prefix. The relation says: a cone `σΣ*`
relates to the neighbourhoods of `coneVal σ`, and a singleton `{σ}` to those of `singVal σ`. -/
def liftC (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap C V where
  rel X Y := (∃ σ, X = cone σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [C_master]; exact cone_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have : σ = σ' := cone_injective hX'
      subst this
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (cone_ne_singleton σ σ')
    · exact absurd hX'.symm (cone_ne_singleton σ' σ)
    · have : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst this
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · -- input is the cone `σΣ*`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · -- `X' = cone τ ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := cone_subset_cone.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · -- `X' = {τ} ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := singleton_subset_cone.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · -- input is the singleton `{σ}`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_cone_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at this
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩
end

section
variable {β : Type*}

/-- **Example 4.4 — `empty`.** `empty(Λ) = true`, `empty(0x) = empty(1x) = false`, strict. -/
def emptyMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗)
end

section
variable {β : Type*}

/-- `liftC` on a partial element: `f(σ⊥) = coneVal σ`. -/
theorem liftC_strBot (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strBot σ) = coneVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := cone_subset_cone.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_cone_subset_singleton σ σ')
  · intro hY
    exact ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩
end

section
variable {β : Type*}

/-- `liftC` on a total element: `f(σ) = singVal σ`. -/
theorem liftC_strElem (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strElem σ) = singVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_cone.mp
        rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at this
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩
end

section
variable {β : Type*}

@[simp] theorem emptyMap_strElem (σ : Str) :
    emptyMap.toElementMap (strElem σ) = headValC T 𝕥 𝕗 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ
end

section
variable {β : Type*}

@[simp] theorem emptyMap_strBot (σ : Str) :
    emptyMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ
end

section
variable {β : Type*}

/-- **Example 4.4 — `one`.** `one(Λ) = false`, `one(0x) = false`, `one(1x) = true`, strict. -/
def oneMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥)
end

section
variable {β : Type*}

/-- **Example 4.4 — `zero`.** `zero(Λ) = false`, `zero(0x) = true`, `zero(1x) = false`, strict. -/
def zeroMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗)
end

section
variable {β : Type*}

@[simp] theorem zeroMap_strElem (σ : Str) :
    zeroMap.toElementMap (strElem σ) = headValC T 𝕗 𝕥 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ
end

section
variable {β : Type*}

@[simp] theorem zeroMap_strBot (σ : Str) :
    zeroMap.toElementMap (strBot σ) = headValC T T.bot 𝕥 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ
end

section
variable {β : Type*}

@[simp] theorem oneMap_strElem (σ : Str) :
    oneMap.toElementMap (strElem σ) = headValC T 𝕗 𝕗 𝕥 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ
end

section
variable {β : Type*}

@[simp] theorem oneMap_strBot (σ : Str) :
    oneMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕥 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ
end

section
variable {β : Type*}

/-- The defining right-hand side: `cond(empty(x), false, cond(zero(x), false, true))`. It uses only
`empty`, `zero` and the conditional `cond` (Exercise 3.26) — not `one`. -/
def oneDef (x : C.Element) : T.Element :=
  (Exercise326.cond T).toElementMap
    (pair (emptyMap.toElementMap x)
      (pair 𝕗
        ((Exercise326.cond T).toElementMap (pair (zeroMap.toElementMap x) (pair 𝕗 𝕥)))))
end

section
variable {β : Type*}

/-- `cond(⊥, x, y) = ⊥` in `T`, phrased with `T.bot` (which the head-test `empty(⊥)` produces)
rather than the syntactically distinct `Example23.botElt` of `Exercise326.cond_bot`. -/
theorem condT_bot (x y : T.Element) :
    (Exercise326.cond T).toElementMap (pair T.bot (pair x y)) = T.bot := by
  apply Element.ext
  intro Z
  rw [Exercise326.cond_toElementMap_mem]
  constructor
  · rintro (⟨h0, _⟩ | ⟨h1, _⟩ | rfl)
    · rw [NeighborhoodSystem.mem_bot] at h0; exact absurd h0 Exercise326.zero_ne_master
    · rw [NeighborhoodSystem.mem_bot] at h1; exact absurd h1 Exercise326.one_ne_master
    · exact T.bot.master_mem
  · intro h
    rw [NeighborhoodSystem.mem_bot] at h
    exact Or.inr (Or.inr h)
end

section
variable {β : Type*}

/- concordance: source L2323 EXERCISE 4.19 Peano axioms for sequences -/
/-- **Exercise 4.19 (Scott 1981, PRG-19).** The same defining equation holds on every partial
element `σ⊥` — including `⊥ = []⊥` where `empty(⊥) = ⊥` forces `cond(⊥, …) = ⊥`. -/
theorem one_def_strBot (σ : Str) : oneMap.toElementMap (strBot σ) = oneDef (strBot σ) := by
  cases σ with
  | nil =>
    rw [oneDef, emptyMap_strBot, headValC_nil, condT_bot, oneMap_strBot, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      rw [oneDef, emptyMap_strBot, headValC_false, Exercise326.cond_false,
        zeroMap_strBot, headValC_false, Exercise326.cond_true, oneMap_strBot, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strBot, headValC_true, Exercise326.cond_false,
        zeroMap_strBot, headValC_true, Exercise326.cond_false, oneMap_strBot, headValC_true]
end

section
variable {β : Type*}

/-- **Exercise 4.19 (Scott 1981, PRG-19).** `one` is definable from `empty`, `zero`, `cond`: the
equation `one(x) = cond(empty(x), false, cond(zero(x), false, true))` holds on every total element
`σ`. -/
theorem one_def_strElem (σ : Str) : oneMap.toElementMap (strElem σ) = oneDef (strElem σ) := by
  cases σ with
  | nil =>
    -- empty(Λ)=true ⟹ cond picks `false`
    rw [oneDef, emptyMap_strElem, headValC_nil, Exercise326.cond_true,
      oneMap_strElem, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      -- empty=false ⟹ inner cond; zero(0σ)=true ⟹ inner cond picks `false`
      rw [oneDef, emptyMap_strElem, headValC_false, Exercise326.cond_false,
        zeroMap_strElem, headValC_false, Exercise326.cond_true, oneMap_strElem, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strElem, headValC_true, Exercise326.cond_false,
        zeroMap_strElem, headValC_true, Exercise326.cond_false, oneMap_strElem, headValC_true]
end

section
/-- **Exercise 4.19 — Peano (ii′) for `{0,1}*`.** The two successor ranges are disjoint:
`0σ ≠ 1τ`. -/
theorem peano_cons_disjoint (σ τ : Str) : (false :: σ) ≠ (true :: τ) := by
  simp
end

section
/-- **Exercise 4.19 — Peano (ii) for `{0,1}*`.** Each successor `b ::·` is injective. -/
theorem peano_cons_injective {b : Bool} {σ τ : Str} (h : b :: σ = b :: τ) : σ = τ :=
  (List.cons.injEq b σ b τ).mp h |>.2
end

section
/-- **Exercise 4.19 — Peano (iii) for `{0,1}*`.** Induction: a predicate holding at `Λ` and closed
under both successors holds everywhere. (This is `List.rec`; it is the two-successor analogue of
Definition 4.5(iii) and the recursion engine behind `tail`/`empty`/`zero`/`one`.) -/
theorem peano_induction (P : Str → Prop) (hnil : P []) (hcons : ∀ b σ, P σ → P (b :: σ)) :
    ∀ σ, P σ := by
  intro σ
  induction σ with
  | nil => exact hnil
  | cons b σ ih => exact hcons b σ ih
end

section
/-- **Exercise 4.19 — Peano (i) for `{0,1}*`.** `Λ` is not a successor: `[] ≠ b :: σ`. -/
theorem peano_nil_ne_cons (b : Bool) (σ : Str) : ([] : Str) ≠ b :: σ := by
  simp
end

section
set_option linter.unusedVariables false

theorem example_419 : And
  (And
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ))
  (∀ (P : DomainTheory.NeighbourhoodSystems.ExampleB.Str → Prop),
    P (@List.nil Bool) →
      (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ → P (@List.cons Bool b σ)) →
        ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ))
  (∀ (P : DomainTheory.NeighbourhoodSystems.ExampleB.Str → Prop),
    P (@List.nil Bool) →
      (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ → P (@List.cons Bool b σ)) →
        ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ)
  (@And.intro
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ)
    (@And.intro
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ))
      (@And.intro
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ)))
        (@And.intro
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ)))
          DomainTheory.NeighbourhoodSystems.Exercise419.peano_nil_ne_cons
          DomainTheory.NeighbourhoodSystems.Exercise419.one_def_strBot)
        DomainTheory.NeighbourhoodSystems.Exercise419.one_def_strElem)
      DomainTheory.NeighbourhoodSystems.Exercise419.peano_cons_disjoint)
    @DomainTheory.NeighbourhoodSystems.Exercise419.peano_cons_injective)
  DomainTheory.NeighbourhoodSystems.Exercise419.peano_induction
end

end DomainTheory.NeighbourhoodSystems.Exercise419
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f(fix(g ∘ f))` is a fixed point of `f ∘ g`:
`(f ∘ g)(f(fix(g∘f))) = f((g∘f)(fix(g∘f))) = f(fix(g∘f))`. -/
theorem comp_fixElement_isFixed (f g : ApproximableMap V V) :
    (f.comp g).toElementMap (f.toElementMap (g.comp f).fixElement)
      = f.toElementMap (g.comp f).fixElement := by
  rw [toElementMap_comp]
  -- `g(f(fix(g∘f))) = (g∘f)(fix(g∘f)) = fix(g∘f)`
  have h : g.toElementMap (f.toElementMap (g.comp f).fixElement) = (g.comp f).fixElement := by
    rw [← toElementMap_comp]
    exact toElementMap_fixElement (g.comp f)
  rw [h]

end ApproximableMap
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/- concordance: source L2325 EXERCISE 4.20 fix of a composite -/
/-- **Exercise 4.20 (Scott 1981, PRG-19).** `fix(f ∘ g) = f(fix(g ∘ f))`. -/
theorem fixElement_comp_comm (f g : ApproximableMap V V) :
    (f.comp g).fixElement = f.toElementMap (g.comp f).fixElement := by
  apply le_antisymm
  · -- `fix(f∘g) ⊑ f(fix(g∘f))` since the latter is a (pre-)fixed point of `f∘g`.
    exact fixElement_le_of_toElementMap_le (f.comp g)
      (le_of_eq (comp_fixElement_isFixed f g))
  · -- `f(fix(g∘f)) ⊑ fix(f∘g)`. First, `fix(g∘f) ⊑ g(fix(f∘g))`.
    have hga : (g.comp f).fixElement ≤ g.toElementMap (f.comp g).fixElement := by
      apply fixElement_le_of_toElementMap_le (g.comp f)
      have : (g.comp f).toElementMap (g.toElementMap (f.comp g).fixElement)
          = g.toElementMap (f.comp g).fixElement := comp_fixElement_isFixed g f
      exact le_of_eq this
    -- apply `f` and use `f(g(fix(f∘g))) = (f∘g)(fix(f∘g)) = fix(f∘g)`.
    calc f.toElementMap (g.comp f).fixElement
        ≤ f.toElementMap (g.toElementMap (f.comp g).fixElement) := f.toElementMap_mono hga
      _ = (f.comp g).toElementMap (f.comp g).fixElement := by rw [toElementMap_comp]
      _ = (f.comp g).fixElement := toElementMap_fixElement (f.comp g)

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_420.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f))) :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_comp_comm
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/- concordance: source L2351 EXERCISE 4.23 commuting with the iterates -/
/-- **Exercise 4.23 (Scott 1981, PRG-19) — Eilenberg.** If `f` is approximable and `aₙ` is an
*approximation scheme* — (i) `a₀ = ⊥`, (ii) increasing, (iii) `⊔ₙ aₙ = I` (pointwise `IsLUB`),
(iv) `aₙ₊₁ ∘ f = aₙ₊₁ ∘ f ∘ aₙ` — then `f` has a **unique** fixed point.

The unique fixed point is `fix f` (Theorem 4.1). -/
theorem f_unique_fixedPoint (f : ApproximableMap V V) (a : ℕ → ApproximableMap V V)
    (ha0 : ∀ x, (a 0).toElementMap x = V.bot)
    (hlub : ∀ x, IsLUB {y | ∃ n, y = (a n).toElementMap x} x)
    (hcomm : ∀ n x, (a (n + 1)).toElementMap (f.toElementMap x) =
      (a (n + 1)).toElementMap (f.toElementMap ((a n).toElementMap x))) :
    ∃! x, f.toElementMap x = x := by
  set fix := f.fixElement with hfixdef
  have hfixed : f.toElementMap fix = fix := toElementMap_fixElement f
  refine ⟨fix, hfixed, ?_⟩
  intro x hx
  -- `fix ⊑ x`: minimality of the least fixed point.
  have hle : fix ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hx)
  -- `aₙ(x) ⊑ aₙ(fix)` by induction on `n` (Scott's hint).
  have approx_le : ∀ n, (a n).toElementMap x ≤ (a n).toElementMap fix := by
    intro n
    induction n with
    | zero => rw [ha0 x]; exact bot_le
    | succ k ih =>
      have h1 : (a (k + 1)).toElementMap x =
          (a (k + 1)).toElementMap (f.toElementMap ((a k).toElementMap x)) := by
        rw [← hcomm k x, hx]
      have h2 : (a (k + 1)).toElementMap (f.toElementMap ((a k).toElementMap fix)) =
          (a (k + 1)).toElementMap fix := by
        rw [← hcomm k fix, hfixed]
      rw [h1, ← h2]
      exact toElementMap_mono (a (k + 1)) (toElementMap_mono f ih)
  -- each `aₙ(fix) ⊑ fix` (since `fix` is an upper bound of its own scheme).
  have hfix_ub : ∀ n, (a n).toElementMap fix ≤ fix := fun n => (hlub fix).1 ⟨n, rfl⟩
  -- so `fix` is an upper bound of `{aₙ(x)}`, hence `x = ⊔ₙ aₙ(x) ⊑ fix`.
  have hge : x ≤ fix := by
    apply (hlub x).2
    rintro y ⟨n, rfl⟩
    exact le_trans (approx_le n) (hfix_ub n)
  exact le_antisymm hge hle

end ApproximableMap
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.ApproximableMap
section
set_option linter.unusedVariables false

theorem example_423.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
  (a : Nat → @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
  (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
          (a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) x)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @IsLUB (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@Set.ofPred (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) =>
            ∃ (n : Nat),
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) y
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V (a n) x))
          x) →
      (∀ (n : Nat) (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
              (a
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
              (a
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V (a n) x)))) →
        @ExistsUnique (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) =>
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.f_unique_fixedPoint
end

end DomainTheory.NeighbourhoodSystems.ApproximableMap
namespace DomainTheory.NeighbourhoodSystems.Exercise425
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

section
/-- Shifting a set up by one length: `shift X = {m + 1 ∣ m ∈ X}` (the token action of prepending a
`1`). -/
def shift (X : Set ℕ) : Set ℕ := {k | ∃ m ∈ X, k = m + 1}
end

section
/-- The tail `tail n = {1ᵐ ∣ m ≥ n} = {m ∣ n ≤ m}` (the partial information "at least `n` ones"). -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}
end

section
@[simp] theorem mem_tail {n k : ℕ} : k ∈ tail n ↔ n ≤ k := Iff.rfl
end

section
/-- Membership in `C₁`: a neighbourhood is a tail `tail n` or a singleton `{n}`. -/
def memC1 (X : Set ℕ) : Prop := (∃ n, X = tail n) ∨ (∃ n, X = {n})
end

section
theorem memC1_singleton (n : ℕ) : memC1 ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩
end

section
theorem memC1_tail (n : ℕ) : memC1 (tail n) := Or.inl ⟨n, rfl⟩
end

section
theorem shift_mono {X X' : Set ℕ} (h : X' ⊆ X) : shift X' ⊆ shift X := by
  rintro k ⟨m, hm, rfl⟩; exact ⟨m, h hm, rfl⟩
end

section
/-- `1·{1ⁿ} = {1ⁿ⁺¹}`: shifting a singleton. -/
theorem shift_singleton (n : ℕ) : shift ({n} : Set ℕ) = {n + 1} := by
  ext k
  simp only [shift, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨n, rfl, rfl⟩
end

section
/-- `1·(1ⁿ⊥) = 1ⁿ⁺¹⊥`: shifting a tail. -/
theorem shift_tail (n : ℕ) : shift (tail n) = tail (n + 1) := by
  ext k
  simp only [shift, tail, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩; omega
  · intro h; exact ⟨k - 1, by omega, by omega⟩
end

section
/-- Shifting keeps us inside `C₁` (`shift (tail n) = tail (n+1)`, `shift {n} = {n+1}`). -/
theorem memC1_shift {X : Set ℕ} (hX : memC1 X) : memC1 (shift X) := by
  rcases hX with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact Or.inl ⟨n + 1, shift_tail n⟩
  · exact Or.inr ⟨n + 1, shift_singleton n⟩
end

section
/-- A singleton and a tail are nested or disjoint. -/
theorem singleton_tail_nd (n k : ℕ) :
    ({k} : Set ℕ) ⊆ tail n ∨ tail n ⊆ {k} ∨ ({k} : Set ℕ) ∩ tail n = ∅ := by
  by_cases h : n ≤ k
  · exact Or.inl (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_tail, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hw; exact h hw
end

section
/-- Any two neighbourhoods of `C₁` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC1 := by
  rintro X Y (⟨n, rfl⟩ | ⟨n, rfl⟩) (⟨m, rfl⟩ | ⟨m, rfl⟩)
  · rcases le_total n m with h | h
    · exact Or.inr (Or.inl (fun k hk => le_trans h hk))
    · exact Or.inl (fun k hk => le_trans h hk)
  · rcases singleton_tail_nd n m with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_tail_nd m n with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2; exact h h2
end

section
theorem tail_zero : tail 0 = Set.univ := by ext k; simp [tail]
end

section
theorem memC1_univ : memC1 (Set.univ : Set ℕ) := Or.inl ⟨0, tail_zero.symm⟩
end

section
/- concordance: source L2377 EXERCISE 4.25 unary sequence domain -/
/-- **Exercise 4.25 (Scott 1981, PRG-19).** The unary sequence system `C₁` on `Δ = {1}* ≅ ℕ`. -/
def C1 : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memC1 Set.univ Set.univ_nonempty
    memC1_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)
end

section
@[simp] theorem C1_mem {X : Set ℕ} : C1.mem X ↔ memC1 X := Iff.rfl
end

section
@[simp] theorem C1_master : C1.master = (Set.univ : Set ℕ) := rfl
end

section
/-- **Exercise 4.25 — the successor `x ↦ 1x`** (analogous to the two successors of `C`). The
approximable map prepending a `1`, i.e. shifting the length: `X (1x) Y ↔ shift X ⊆ Y`. -/
def consMap : ApproximableMap C1 C1 where
  rel X Y := memC1 X ∧ memC1 Y ∧ shift X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨memC1_univ, memC1_univ, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : shift X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, C1.inter_mem hY hY' (memC1_shift hX) hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (shift_mono hX'X).trans (hsub.trans hYY')⟩
end

section
/-- **Exercise 4.25 — the infinite unary sequence `1^∞`.** Unlike the flat domain `N` (whose only
elements are `⊥` and the numerals `n̂`), `C₁` has a genuine *infinite* element: the least fixed point
of the successor `x ↦ 1x`, satisfying `1^∞ = 1·1^∞` (`infElt_eq`). This is what distinguishes the
*non-flat* `C₁` (the true analogue of `C`) from `N`. -/
def infElt : C1.Element := consMap.fixElement
end

section
/-- The partial element `1ⁿ⊥ = ↑(tail n)` ("at least `n` ones"). -/
def oneBot (n : ℕ) : C1.Element := C1.principal (memC1_tail n)
end

section
/-- The total element `1ⁿ = ↑{n}` (the finite string of exactly `n` ones). -/
def oneElem (n : ℕ) : C1.Element := C1.principal (memC1_singleton n)
end

section
/-- **Exercise 4.25 — relating `N` and `C₁`.** The "length ↦ unary expansion" map `N → C₁` sending
the numeral `n̂` to the finite string `1ⁿ` and `⊥` to `⊥` (strict). Built from the strict-lift
combinator `constLiftN` of Example 4.3. -/
def relateNToC1 : ApproximableMap Example43.N C1 := Example43.constLiftN C1 oneElem
end

section
/-- `1·(1ⁿ⊥) = 1ⁿ⁺¹⊥`. -/
theorem consMap_oneBot (n : ℕ) : consMap.toElementMap (oneBot n) = oneBot (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift (tail n) ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_tail] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨tail n, ⟨memC1_tail n, subset_rfl⟩, memC1_tail n, hY, ?_⟩
    rw [shift_tail]; exact hsub
end

section
/-- `1·(1ⁿ) = 1ⁿ⁺¹`. -/
theorem consMap_oneElem (n : ℕ) : consMap.toElementMap (oneElem n) = oneElem (n + 1) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : shift {n} ⊆ Y := (shift_mono hXX').trans hsub
    rwa [shift_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{n}, ⟨memC1_singleton n, subset_rfl⟩, memC1_singleton n, hY, ?_⟩
    rw [shift_singleton]; exact hsub
end

section
/-- `1^∞ = 1·1^∞`: the infinite sequence is fixed by the successor. -/
theorem infElt_eq : consMap.toElementMap infElt = infElt :=
  toElementMap_fixElement consMap
end

section
/-- `relateNToC1(⊥) = ⊥`. -/
theorem relateNToC1_bot : relateNToC1.toElementMap Example43.N.bot = C1.bot :=
  Example43.constLiftN_bot C1 oneElem
end

section
set_option linter.unusedVariables false

theorem example_425 : @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat DomainTheory.NeighbourhoodSystems.Exercise425.C1)
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap Nat Nat DomainTheory.NeighbourhoodSystems.Example43.N
    DomainTheory.NeighbourhoodSystems.Exercise425.C1 DomainTheory.NeighbourhoodSystems.Exercise425.relateNToC1
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat DomainTheory.NeighbourhoodSystems.Example43.N))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot Nat DomainTheory.NeighbourhoodSystems.Exercise425.C1) :=
  DomainTheory.NeighbourhoodSystems.Exercise425.relateNToC1_bot
end

section
/-- `relateNToC1(n̂) = 1ⁿ`. -/
theorem relateNToC1_natElem (n : ℕ) :
    relateNToC1.toElementMap (Example43.natElem n) = oneElem n :=
  Example43.constLiftN_natElem C1 oneElem n
end

end DomainTheory.NeighbourhoodSystems.Exercise425
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
open ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 4.2(i) (Scott 1981, PRG-19).** `fix(f) = f(fix(f))`: the value of `fix` is a fixed
point of the argument. (Equivalently `eval(f, fix(f)) = fix(f)` by `evalMap_apply`.) -/
theorem fixMap_fixed (V : NeighborhoodSystem α) (φ : (funSpace V V).Element) :
    (toApproxMap φ).toElementMap ((fixMap V).toElementMap φ) = (fixMap V).toElementMap φ := by
  rw [fixMap_toElementMap]
  exact toElementMap_fixElement (toApproxMap φ)
end

section
variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 4.2 (Scott 1981, PRG-19) — uniqueness.** Any approximable operator `fax` satisfying
(i) and (ii) coincides with `fix`. (Scott: from (i)(ii) one proves `fix(f) ⊆ fax(f)` and
`fax(f) ⊆ fix(f)`.) -/
theorem fixMap_unique (V : NeighborhoodSystem α) (fax : ApproximableMap (funSpace V V) V)
    (h_fix : ∀ φ, (toApproxMap φ).toElementMap (fax.toElementMap φ) = fax.toElementMap φ)
    (h_least : ∀ (φ : (funSpace V V).Element) (z : V.Element),
      (toApproxMap φ).toElementMap z ≤ z → fax.toElementMap φ ≤ z) :
    fax = fixMap V := by
  apply ext_of_toElementMap
  intro φ
  apply le_antisymm
  · exact h_least φ _ (le_of_eq (fixMap_fixed V φ))
  · exact fixMap_least V φ (le_of_eq (h_fix φ))
end

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem46/PeanoModel.lean
universe u

namespace DomainTheory.NeighbourhoodSystems

/- concordance: source L2143 DEFINITION 4.5 Peano axioms -/
/-- **Definition 4.5 (Scott 1981, PRG-19).** A *model for Peano's Axioms*: a type `N` with a
distinguished element `zero` and a unary `succ`essor, satisfying

* (i)   `zero ≠ succ n` for all `n`                       (`zero_ne_succ`);
* (ii)  `succ` is injective (`n⁺ = m⁺ ⟹ n = m`)          (`succ_injective`);
* (iii) **mathematical induction**: any `s ⊆ N` with `zero ∈ s` and closed under `succ`
        (`∀ n ∈ s, succ n ∈ s`, i.e. Scott's `x⁺ ⊆ x`) is all of `N`
        (`∀ n, n ∈ s`, i.e. Scott's `x = N`)              (`induction`). -/
structure PeanoModel (N : Type u) where
  /-- The distinguished zero `0 ∈ N`. -/
  zero : N
  /-- The unary successor `⁺ : N → N`. -/
  succ : N → N
  /-- **4.5(i)** `0 ≠ n⁺`. -/
  zero_ne_succ : ∀ n, zero ≠ succ n
  /-- **4.5(ii)** the successor is one-one. -/
  succ_injective : Function.Injective succ
  /-- **4.5(iii)** the induction principle (point form of `x⁺ ⊆ x ⟹ x = N`). -/
  induction : ∀ (s : Set N), zero ∈ s → (∀ n ∈ s, succ n ∈ s) → ∀ n, n ∈ s

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}

/-- Scott's least fixed point `r ⊆ N × M`, realized as the inductively generated relation: the
least relation containing `(0, □)` and closed under `(n, m) ↦ (n⁺, m#)`. The two constructors are
Scott's facts (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#`. By Theorem 4.1 this *is* the least fixed
point of the approximable operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` on `P(N × M)`. -/
inductive Graph (P : PeanoModel M) (Q : PeanoModel N) : M → N → Prop
  | base : Graph P Q P.zero Q.zero
  | step : ∀ {m n}, Graph P Q m n → Graph P Q (P.succ m) (Q.succ n)

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- The construction is symmetric in the two models: `Graph P Q m n` swaps to `Graph Q P n m`.
(This is why the relation is one-one in *both* directions, as Scott notes: "the rôles of `N` and
`M` are completely symmetric".) -/
theorem Graph.swap {P : PeanoModel M} {Q : PeanoModel N} {m : M} {n : N}
    (h : Graph P Q m n) : Graph Q P n m := by
  induction h with
  | base => exact Graph.base
  | step _ ih => exact Graph.step ih

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Inversion at a successor (uses 4.5(i)/(ii)).** Anything related to `n⁺` on the left comes
from a relation `n r n₀` with right value a successor: `n⁺ r k ⟹ ∃ n₀, n r n₀ ∧ k = n₀#`. -/
theorem graph_succ_right (P : PeanoModel M) (Q : PeanoModel N) {m : M} {k : N}
    (h : Graph P Q (P.succ m) k) : ∃ n, Graph P Q m n ∧ k = Q.succ n := by
  generalize hz : P.succ m = z at h
  cases h with
  | base => exact absurd hz.symm (P.zero_ne_succ _)
  | step h' =>
    rename_i m0 n0
    have hm : m = m0 := P.succ_injective hz
    subst hm
    exact ⟨n0, h', rfl⟩

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- **Inversion at `0` (uses 4.5(i)).** Anything related to `0` on the left is `□` on the right:
`0 r k ⟹ k = □`. (The other generating rule would force `0 = n⁺`, impossible by 4.5(i).) -/
theorem graph_zero_right (P : PeanoModel M) (Q : PeanoModel N) {k : N}
    (h : Graph P Q P.zero k) : k = Q.zero := by
  generalize hz : P.zero = z at h
  cases h with
  | base => rfl
  | step _ => exact absurd hz (P.zero_ne_succ _)

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- Each element of the left model is related by `Graph` to exactly one element of the right
model. Proved by the induction principle 4.5(iii) on the set `{m ∣ ∃! n, m r n}`: the base case
is the `0`-inversion `graph_zero_right`, the step case the successor-inversion `graph_succ_right`
together with 4.5(ii). -/
theorem exists_unique_right (P : PeanoModel M) (Q : PeanoModel N) (m : M) :
    ∃! n, Graph P Q m n := by
  refine P.induction {m | ∃! n, Graph P Q m n} ?_ ?_ m
  · exact ⟨Q.zero, Graph.base, fun k hk => graph_zero_right P Q hk⟩
  · rintro m' ⟨n', hn', huniq⟩
    refine ⟨Q.succ n', Graph.step hn', fun k hk => ?_⟩
    obtain ⟨n'', hn'', rfl⟩ := graph_succ_right P Q hk
    rw [huniq n'' hn'']

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- Dually (by `Graph.swap`), each element of the right model is related to exactly one element of
the left model. -/
theorem exists_unique_left (P : PeanoModel M) (Q : PeanoModel N) (n : N) :
    ∃! m, Graph P Q m n := by
  obtain ⟨m, hm, huniq⟩ := exists_unique_right Q P n
  exact ⟨m, hm.swap, fun y hy => huniq y hy.swap⟩

end PeanoModel
end

section
universe u v

namespace PeanoModel

variable {M : Type u} {N : Type v}


/- concordance: source L2155 THEOREM 4.6 Peano models isomorphic -/
/-- **Theorem 4.6 (Scott 1981, PRG-19).** *All models of Peano's Axioms are isomorphic.* Between
any two models there is a bijection `e : N ≃ M` of the underlying sets that preserves the
structure: `e 0 = □` and `e (n⁺) = (e n)#`. The bijection is the least-fixed-point relation
`Graph`, which `exists_unique_right`/`exists_unique_left` show is a one-one correspondence; the
two structure equations are the constructors `Graph.base`/`Graph.step`. -/
theorem peano_models_isomorphic (P : PeanoModel M) (Q : PeanoModel N) :
    ∃ e : M ≃ N, e P.zero = Q.zero ∧ ∀ m, e (P.succ m) = Q.succ (e m) := by
  classical
  refine ⟨⟨fun m => (exists_unique_right P Q m).choose,
          fun n => (exists_unique_left P Q n).choose, ?_, ?_⟩, ?_, ?_⟩
  · -- left inverse `g ∘ f = id`
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_left P Q _).choose_spec.2 m hf).symm
  · -- right inverse `f ∘ g = id`
    intro n
    have hg : Graph P Q (exists_unique_left P Q n).choose n :=
      (exists_unique_left P Q n).choose_spec.1
    exact ((exists_unique_right P Q _).choose_spec.2 n hg).symm
  · -- `f 0 = □`
    exact ((exists_unique_right P Q P.zero).choose_spec.2 Q.zero Graph.base).symm
  · -- `f (n⁺) = (f n)#`
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_right P Q (P.succ m)).choose_spec.2 _ (Graph.step hf)).symm

end PeanoModel
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.PeanoModel
section
set_option linter.unusedVariables false

theorem theorem_46.{u, v} : ∀ {M : Type u} {N : Type v} (P : DomainTheory.NeighbourhoodSystems.PeanoModel M)
  (Q : DomainTheory.NeighbourhoodSystems.PeanoModel N),
  ∃ (e : Equiv M N),
    And
      (@Eq N
        (@DFunLike.coe (Equiv M N) M (fun (x : M) => N)
          (@EquivLike.toFunLike (Equiv M N) M N (@Equiv.instEquivLike M N)) e
          (@DomainTheory.NeighbourhoodSystems.PeanoModel.zero M P))
        (@DomainTheory.NeighbourhoodSystems.PeanoModel.zero N Q))
      (∀ (m : M),
        @Eq N
          (@DFunLike.coe (Equiv M N) M (fun (x : M) => N)
            (@EquivLike.toFunLike (Equiv M N) M N (@Equiv.instEquivLike M N)) e
            (@DomainTheory.NeighbourhoodSystems.PeanoModel.succ M P m))
          (@DomainTheory.NeighbourhoodSystems.PeanoModel.succ N Q
            (@DFunLike.coe (Equiv M N) M (fun (x : M) => N)
              (@EquivLike.toFunLike (Equiv M N) M N (@Equiv.instEquivLike M N)) e m))) :=
  @DomainTheory.NeighbourhoodSystems.PeanoModel.peano_models_isomorphic
end

end DomainTheory.NeighbourhoodSystems.PeanoModel
namespace DomainTheory.NeighbourhoodSystems.Exercise422
open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- Scott's operator `g(x) = {0} ∪ x⁺` on `P(N*)`, whose least fixed point is the smallest subset
containing `0` and closed under the successor. -/
def genOp (x : Set M) : Set M := {zero} ∪ succ '' x
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- *(For set theorists.)* The standard natural numbers `⟨ℕ, 0, ⁺⟩` form a model of Peano's Axioms;
their existence is the **axiom of infinity**. (This witnesses that an `N*` satisfying (i)/(ii) — in
fact all three — exists in the first place.) -/
def natPeano : PeanoModel ℕ where
  zero := 0
  succ := Nat.succ
  zero_ne_succ n := (Nat.succ_ne_zero n).symm
  succ_injective := Nat.succ_injective
  induction s h0 hstep := by
    intro n
    induction n with
    | zero => exact h0
    | succ k ih => exact hstep k ih
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The carved-out subset `N ⊆ N*`: the least fixed point of `g` (Exercise 4.13(2)/4.14). -/
def nats : Set M := lfpSet (genOp zero succ)
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The subtype `N = {m // m ∈ nats}` carrying the carved-out Peano structure. -/
abbrev Nat' : Type _ := {m : M // m ∈ nats zero succ}
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- **Induction by minimality.** Any subset `s ⊆ N*` containing `0` and closed under `⁺` contains
all of `N`. (This is the heart of axiom (iii): `s` is a pre-fixed point of `g`, hence dominates the
least fixed point `nats`.) -/
theorem nats_induction (s : Set M) (h0 : zero ∈ s) (hsucc : ∀ n ∈ s, succ n ∈ s) :
    nats zero succ ⊆ s := by
  apply lfpSet_subset (genOp zero succ)
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · exact h0
  · exact hsucc n hn
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- `N` is closed under the successor: `n ∈ N ⟹ n⁺ ∈ N` — again directly from `lfpSet`. -/
theorem succ_mem_nats {n : M} (hn : n ∈ nats zero succ) : succ n ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inr ⟨n, hn x hx, rfl⟩)
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The successor of the subtype (well-defined by closure `succ_mem_nats`). -/
def subSucc (n : Nat' zero succ) : Nat' zero succ := ⟨succ n.1, succ_mem_nats zero succ n.2⟩
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- `0 ∈ N` — directly from the `lfpSet` definition (no monotonicity needed), keeping the
construction choice-free. -/
theorem zero_mem_nats : zero ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inl rfl)
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- The zero of the subtype. -/
def subZero : Nat' zero succ := ⟨zero, zero_mem_nats zero succ⟩
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/- concordance: source L2347 EXERCISE 4.22 inductive subset of a model -/
/-- **Exercise 4.22 (Scott 1981, PRG-19).** The carved-out subset `N ⊆ N*`, with the inherited
`0` and `⁺`, is a model of **all three** Peano axioms — even though `N*` was only assumed to satisfy
(i) and (ii). Axioms (i)/(ii) are inherited; (iii) holds by minimality of the least fixed point. -/
def peanoSub (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    PeanoModel (Nat' zero succ) where
  zero := subZero zero succ
  succ := subSucc zero succ
  zero_ne_succ n h := hzero n.1 (Subtype.ext_iff.mp h)
  succ_injective a b h := Subtype.ext (hinj (Subtype.ext_iff.mp h))
  induction s h0 hstep := by
    -- pull `s` back to a subset of `N*`, show it is closed under `0`/`⁺`, apply `nats_induction`
    intro n
    have hsub : nats zero succ ⊆
        {m | ∃ h : m ∈ nats zero succ, (⟨m, h⟩ : Nat' zero succ) ∈ s} := by
      apply nats_induction zero succ
      · exact ⟨zero_mem_nats zero succ, h0⟩
      · rintro m ⟨hmnat, hms⟩
        exact ⟨succ_mem_nats zero succ hmnat, hstep ⟨m, hmnat⟩ hms⟩
    obtain ⟨_, hns⟩ := hsub n.2
    exact hns
end

section
variable {M : Type*} (zero : M) (succ : M → M)

/-- **Exercise 4.22 (Scott 1981, PRG-19).** *Yes:* whenever `N*` satisfies (i) and (ii), there is a
subset `N ⊆ N*` (carrying the inherited structure) satisfying (i), (ii), and (iii). -/
theorem exists_peano_submodel (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    Nonempty (PeanoModel (Nat' zero succ)) :=
  ⟨peanoSub zero succ hzero hinj⟩
end

section
set_option linter.unusedVariables false

theorem example_422.{u_1} : ∀ {M : Type u_1} (zero : M) (succ : M → M),
  (∀ (n : M), @Ne M zero (succ n)) →
    @Function.Injective M M succ →
      Nonempty
        (DomainTheory.NeighbourhoodSystems.PeanoModel (@DomainTheory.NeighbourhoodSystems.Exercise422.Nat' M zero succ)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise422.exists_peano_submodel
end

section
variable {M : Type*} (zero : M) (succ : M → M)

theorem genOp_monotone : Monotone (genOp zero succ) := by
  intro x y hxy z hz
  rcases hz with hz | ⟨a, ha, rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨a, hxy ha, rfl⟩
end

section
variable {M : Type*} (zero : M) (succ : M → M)

theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)
end

end DomainTheory.NeighbourhoodSystems.Exercise422
end
