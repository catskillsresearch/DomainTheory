module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_25

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace Ring
section

open NeighborhoodSystem
variable {A : Type*} [CommRing A]

/- concordance: source L538 EXERCISE 1.26 ideals of a ring -/
/-- **Exercise 1.26 — the basic neighbourhood `I(F)`.** `I(F) = {G ∣ F ⊆ ⟨G⟩}`, the finite sets `G`
whose generated ideal contains `F`. -/
def IFamily (F : Finset A) : Set (Finset A) := {G | (↑F : Set A) ⊆ Ideal.span (↑G : Set A)}

@[simp] theorem mem_IFamily {F G : Finset A} :
    G ∈ IFamily F ↔ (↑F : Set A) ⊆ Ideal.span (↑G : Set A) := Iff.rfl

section
variable [DecidableEq A]

/-- `I(F₁) ∩ I(F₂) = I(F₁ ∪ F₂)`: the system is closed under all binary intersections. -/
theorem IFamily_inter (F₁ F₂ : Finset A) :
    IFamily F₁ ∩ IFamily F₂ = IFamily (F₁ ∪ F₂) := by
  ext G
  simp only [IFamily, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_union, Set.union_subset_iff]
end

/-- Inclusion of neighbourhoods reversed to ideal generation: `I(F₁) ⊆ I(F₂) ↔ F₂ ⊆ ⟨F₁⟩`. -/
theorem IFamily_subset_iff (F₁ F₂ : Finset A) :
    IFamily F₁ ⊆ IFamily F₂ ↔ (↑F₂ : Set A) ⊆ Ideal.span (↑F₁ : Set A) := by
  constructor
  · intro h
    have hF₁ : F₁ ∈ IFamily F₁ := mem_IFamily.mpr Ideal.subset_span
    exact (h hF₁)
  · intro h G hG
    rw [mem_IFamily] at hG ⊢
    exact h.trans (SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr hG))

section
variable [DecidableEq A]

/-- **Exercise 1.26 — the neighbourhood system of a commutative ring.** Tokens are finite subsets
`F ⊆ A`; neighbourhoods are the sets `I(F)`. The master is `I(∅)` (all of `Δ`), and intersections
`I(F₁) ∩ I(F₂) = I(F₁ ∪ F₂)` are always neighbourhoods. -/
def ringSystem : NeighborhoodSystem (Finset A) where
  mem S := ∃ F, S = IFamily F
  master := IFamily ∅
  master_nonempty := ⟨∅, by simp [IFamily]⟩
  master_mem := ⟨∅, rfl⟩
  inter_mem := by
    rintro X Y Z ⟨F₁, rfl⟩ ⟨F₂, rfl⟩ _ _
    exact ⟨F₁ ∪ F₂, IFamily_inter F₁ F₂⟩
  sub_master := by
    rintro X ⟨F, rfl⟩
    exact (IFamily_subset_iff F ∅).mpr (by rw [Finset.coe_empty]; exact Set.empty_subset _)

@[simp] theorem ringSystem_mem {S : Set (Finset A)} :
    (ringSystem (A := A)).mem S ↔ ∃ F, S = IFamily F := Iff.rfl

theorem IFamily_mem (F : Finset A) : (ringSystem (A := A)).mem (IFamily F) := ⟨F, rfl⟩

/-- **Exercise 1.26 — the ideal of a filter.** `idealOf x = {a ∣ I({a}) ∈ x}`. The closure
properties of an ideal come from the filter axioms: `0` from the master, `+` from `∩`-closure
(`I({a}) ∩ I({b}) = I({a,b}) ⊆ I({a+b})`), and `•` from upward closure (`I({a}) ⊆ I({c·a})`). -/
def idealOf (x : (ringSystem (A := A)).Element) : Ideal A where
  carrier := {a | x.mem (IFamily {a})}
  zero_mem' := by
    show x.mem (IFamily {(0 : A)})
    refine x.up_mem x.master_mem (IFamily_mem {(0 : A)}) ?_
    intro G _
    rw [mem_IFamily, Finset.coe_singleton, Set.singleton_subset_iff]
    exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    show x.mem (IFamily {a + b})
    have h := x.inter_mem ha hb
    rw [IFamily_inter] at h
    refine x.up_mem h (IFamily_mem {a + b}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_union,
      Finset.coe_singleton, Finset.coe_singleton]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  smul_mem' := by
    intro c a ha
    show x.mem (IFamily {c • a})
    refine x.up_mem ha (IFamily_mem {c • a}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_singleton]
    exact Submodule.smul_mem _ c (Ideal.subset_span (Set.mem_singleton a))

@[simp] theorem mem_idealOf {x : (ringSystem (A := A)).Element} {a : A} :
    a ∈ idealOf x ↔ x.mem (IFamily {a}) := Iff.rfl

/-- A filter contains `I(F)` whenever it contains `I({a})` for every `a ∈ F` (by `∩`-closure). -/
theorem mem_IFamily_of_forall (x : (ringSystem (A := A)).Element) (F : Finset A)
    (h : ∀ a ∈ F, x.mem (IFamily {a})) : x.mem (IFamily F) := by
  classical
  induction F using Finset.induction with
  | empty => exact x.master_mem
  | @insert a F' _ ih =>
    have hins : (insert a F' : Finset A) = {a} ∪ F' := by
      ext y; simp [Finset.mem_insert]
    rw [hins, ← IFamily_inter]
    exact x.inter_mem (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- **Exercise 1.26 — the filter of an ideal.** `ofIdeal J = {I(F) ∣ ↑F ⊆ J}`. -/
def ofIdeal (J : Ideal A) : (ringSystem (A := A)).Element where
  mem S := ∃ F, S = IFamily F ∧ Ideal.span (↑F : Set A) ≤ J
  sub := by rintro S ⟨F, rfl, _⟩; exact ⟨F, rfl⟩
  master_mem := by
    refine ⟨∅, rfl, ?_⟩
    rw [Finset.coe_empty, Ideal.span_empty]
    exact bot_le
  inter_mem := by
    rintro X Y ⟨F₁, rfl, h₁⟩ ⟨F₂, rfl, h₂⟩
    refine ⟨F₁ ∪ F₂, IFamily_inter F₁ F₂, ?_⟩
    rw [Finset.coe_union, Ideal.span_union]
    exact sup_le h₁ h₂
  up_mem := by
    rintro X Y ⟨F, rfl, hF⟩ ⟨F', rfl⟩ hXY
    refine ⟨F', rfl, ?_⟩
    have hsub : (↑F' : Set A) ⊆ Ideal.span (↑F : Set A) := (IFamily_subset_iff F F').mp hXY
    exact (Ideal.span_le.mpr hsub).trans hF

theorem ofIdeal_idealOf (x : (ringSystem (A := A)).Element) : ofIdeal (idealOf x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro S
  constructor
  · rintro ⟨F, rfl, hF⟩
    refine mem_IFamily_of_forall x F (fun a ha => ?_)
    have haspan : a ∈ Ideal.span (↑F : Set A) := Ideal.subset_span (by simpa using ha)
    exact mem_idealOf.mp (hF haspan)
  · intro hS
    obtain ⟨F, rfl⟩ := x.sub hS
    refine ⟨F, rfl, ?_⟩
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, mem_idealOf]
    refine x.up_mem hS (IFamily_mem {a}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Ideal.subset_span ha
end

theorem span_eq_of_IFamily_eq {F₁ F₂ : Finset A} (h : IFamily F₁ = IFamily F₂) :
    Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A) := by
  have h12 : (↑F₂ : Set A) ⊆ Ideal.span (↑F₁ : Set A) :=
    (IFamily_subset_iff F₁ F₂).mp h.le
  have h21 : (↑F₁ : Set A) ⊆ Ideal.span (↑F₂ : Set A) :=
    (IFamily_subset_iff F₂ F₁).mp h.ge
  exact le_antisymm (Ideal.span_le.mpr h21) (Ideal.span_le.mpr h12)

section
variable [DecidableEq A]

theorem mem_ofIdeal_IFamily (J : Ideal A) (F : Finset A) :
    (ofIdeal J).mem (IFamily F) ↔ Ideal.span (↑F : Set A) ≤ J := by
  constructor
  · rintro ⟨F', hF', hle⟩
    rw [span_eq_of_IFamily_eq hF']
    exact hle
  · intro h
    exact ⟨F, rfl, h⟩

theorem idealOf_ofIdeal (J : Ideal A) : idealOf (ofIdeal J) = J := by
  apply SetLike.ext
  intro a
  rw [mem_idealOf, mem_ofIdeal_IFamily, Finset.coe_singleton, Ideal.span_singleton_le_iff_mem]

/-- **Exercise 1.26 — `|𝒟| ≅ (Ideals A, ⊆)`.** The domain of the ring's neighbourhood system is
order-isomorphic to the ideals of `A` ordered by inclusion, via `x ↦ {a ∣ I({a}) ∈ x}`. -/
def ringIso : (ringSystem (A := A)).Element ≃o Ideal A where
  toFun := idealOf
  invFun := ofIdeal
  left_inv := ofIdeal_idealOf
  right_inv := idealOf_ofIdeal
  map_rel_iff' := by
    intro x y
    constructor
    · intro h S hS
      obtain ⟨F, rfl⟩ := x.sub hS
      refine mem_IFamily_of_forall y F (fun a ha => ?_)
      have hax : a ∈ idealOf x := by
        rw [mem_idealOf]
        exact x.up_mem hS (IFamily_mem {a}) <| (IFamily_subset_iff _ _).mpr <| by
          rw [Finset.coe_singleton, Set.singleton_subset_iff]
          exact Ideal.subset_span (by simpa using ha)
      exact mem_idealOf.mp (h hax)
    · intro h a ha
      exact h (IFamily {a}) ha
end

theorem IFamily_eq_of_span_eq {F₁ F₂ : Finset A}
    (h : Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A)) : IFamily F₁ = IFamily F₂ := by
  apply Set.Subset.antisymm
  · exact (IFamily_subset_iff F₁ F₂).mpr (by rw [h]; exact Ideal.subset_span)
  · exact (IFamily_subset_iff F₂ F₁).mpr (by rw [← h]; exact Ideal.subset_span)
end

end Ring
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Ring
section

set_option linter.unusedVariables false

theorem example_126.{u_1} : ∀ {A : Type u_1} [inst : CommRing A] {F₁ F₂ : Finset A},
  @Eq (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
      (@Ideal.span A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A) F₁))
      (@Ideal.span A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A) F₂)) →
    @Eq (Set (Finset A)) (@DomainTheory.NeighbourhoodSystems.Ring.IFamily A inst F₁)
      (@DomainTheory.NeighbourhoodSystems.Ring.IFamily A inst F₂) :=
  @DomainTheory.NeighbourhoodSystems.Ring.IFamily_eq_of_span_eq
end

end DomainTheory.NeighbourhoodSystems.Ring
end
