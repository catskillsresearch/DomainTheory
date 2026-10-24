module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example_4_4
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_19
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_21
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_10
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise_5_16
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem_5_6
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Computability.MyhillNerode
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_12
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_22
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma_6_15

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_27

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap Subsystem
section
variable {α : Type*} {D E : NeighborhoodSystem α}
namespace Subsystem.ProjectionPair
/- concordance: source L4175 EXERCISE 6.25 projection pair laws -/
/-- **Exercise 6.25 — `g` maps consistent sets to consistent sets.** "Consistent" for sets of
elements is "bounded" (Exercise 1.27). If `S` is bounded by `b`, its image `{g(s) ∣ s ∈ S}` is
bounded by `g(b)` (monotonicity). -/
theorem inj_bounded (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    E.Bounded (P.inj.toElementMap '' S) := by
  obtain ⟨b, hb⟩ := hS
  refine ⟨P.inj.toElementMap b, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact P.inj.toElementMap_mono (hb s hs)

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`g(h(y)) ⊑ y`.** The second projection-pair law `g ∘ h ⊆ I_ℰ`, read on elements. -/
theorem inj_proj_apply_le (P : ProjectionPair D E) (y : E.Element) :
    P.inj.toElementMap (P.proj.toElementMap y) ≤ y := by
  have h := (le_iff_toElementMap_le.mp P.inj_comp_proj_le) y
  rwa [toElementMap_comp, toElementMap_idMap] at h

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`h(g(x)) = x`.** The first projection-pair law `h ∘ g = I_𝒟`, read on elements. -/
theorem proj_inj_apply (P : ProjectionPair D E) (x : D.Element) :
    P.proj.toElementMap (P.inj.toElementMap x) = x := by
  rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **Exercise 6.25, the Galois connection.** For `x ∈ |𝒟|`, `y ∈ |ℰ|`:
`g(x) ⊑ y ↔ x ⊑ h(y)`. So `g` (lower adjoint) and `h` (upper adjoint) determine each other.

`→`: apply the monotone `h` to `g(x) ⊑ y` and use `h(g(x)) = x`.
`←`: apply the monotone `g` to `x ⊑ h(y)` and use `g(h(y)) ⊑ y`. -/
theorem galois (P : ProjectionPair D E) (x : D.Element) (y : E.Element) :
    P.inj.toElementMap x ≤ y ↔ x ≤ P.proj.toElementMap y := by
  constructor
  · intro hxy
    have := P.proj.toElementMap_mono hxy
    rwa [P.proj_inj_apply x] at this
  · intro hxy
    exact (P.inj.toElementMap_mono hxy).trans (P.inj_proj_apply_le y)

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — `g` preserves `⊔` (not just *directed* unions).** For any bounded set `S`,
`g(⊔S) = ⊔ {g(s) ∣ s ∈ S}`. This is the characteristic property of a lower adjoint.

* `⊒`: `g(⊔S)` is an upper bound of `{g(s)}` since `s ⊑ ⊔S` and `g` is monotone.
* `⊑`: by the Galois connection it suffices that `⊔S ⊑ h(⊔{g(s)})`, i.e. that each `s ⊑ h(⊔{g(s)})`;
  by the Galois connection again this is `g(s) ⊑ ⊔{g(s)}`, true by `le_sSup`. -/
theorem inj_sSup (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    P.inj.toElementMap (D.sSup S hS) =
      E.sSup (P.inj.toElementMap '' S) (P.inj_bounded hS) := by
  apply le_antisymm
  · refine (P.galois _ _).mpr (D.sSup_le S hS fun s hs => ?_)
    refine (P.galois s _).mp ?_
    exact E.le_sSup _ (P.inj_bounded hS) ⟨s, hs, rfl⟩
  · refine E.sSup_le _ (P.inj_bounded hS) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact P.inj.toElementMap_mono (D.le_sSup S hS hs)

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- The set `{x ∣ g(x) ⊑ y}` is bounded: `h(y)` is an upper bound (it is in fact the top). -/
theorem lowerSet_bounded (P : ProjectionPair D E) (y : E.Element) :
    D.Bounded (P.lowerSet y) :=
  ⟨P.proj.toElementMap y, fun _ hx => (P.galois _ y).mp hx⟩

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — "check that the set on the right is directed".** Any two members of
`{x ∣ g(x) ⊑ y}` have a common upper bound *inside the set*, namely `h(y)` itself (the down-set of
`h(y)` has `h(y)` as a top, so it is trivially directed). -/
theorem lowerSet_directed (P : ProjectionPair D E) (y : E.Element) :
    ∀ a ∈ P.lowerSet y, ∀ b ∈ P.lowerSet y,
      ∃ c ∈ P.lowerSet y, a ≤ c ∧ b ≤ c := by
  intro a ha b hb
  exact ⟨P.proj.toElementMap y, P.inj_proj_apply_le y,
    (P.galois a y).mp ha, (P.galois b y).mp hb⟩

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25, first extremal formula.** `h(y) = ⊔ {x ∈ |𝒟| ∣ g(x) ⊑ y}`.

`h(y)` is the *greatest* member of the set (`g(h(y)) ⊑ y`, so `h(y)` is in it; every member is
`⊑ h(y)` by the Galois connection), hence it is the least upper bound. -/
theorem proj_eq_sSup (P : ProjectionPair D E) (y : E.Element) :
    P.proj.toElementMap y = D.sSup (P.lowerSet y) (P.lowerSet_bounded y) := by
  apply le_antisymm
  · exact D.le_sSup _ (P.lowerSet_bounded y) (P.inj_proj_apply_le y)
  · exact D.sSup_le _ (P.lowerSet_bounded y) fun x hx => (P.galois x y).mp hx

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25 — "check that the set on the right is non-empty".** `g(x)` itself lies in
`{y ∣ x ⊑ h(y)}`, since `x ⊑ h(g(x)) = x`. -/
theorem upperSet_nonempty (P : ProjectionPair D E) (x : D.Element) :
    (P.upperSet x).Nonempty :=
  ⟨P.inj.toElementMap x, by rw [mem_upperSet, P.proj_inj_apply x]⟩

end Subsystem.ProjectionPair
end

section
variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


/-- **Exercise 6.25, second extremal formula.** `g(x) = ⊓ {y ∈ |ℰ| ∣ x ⊑ h(y)}`.

`g(x)` is the *least* member of the set (`x ⊑ h(g(x)) = x`, so `g(x)` is in it; every member is
`⊒ g(x)` by the Galois connection), hence it is the greatest lower bound. -/
theorem inj_eq_sInf (P : ProjectionPair D E) (x : D.Element) :
    P.inj.toElementMap x = E.sInf (P.upperSet x) (P.upperSet_nonempty x) := by
  apply le_antisymm
  · exact E.le_sInf _ (P.upperSet_nonempty x) _ fun y hy => (P.galois x y).mpr hy
  · refine E.sInf_le _ (P.upperSet_nonempty x) ?_
    rw [mem_upperSet, P.proj_inj_apply x]

end Subsystem.ProjectionPair
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair
section
set_option linter.unusedVariables false

theorem example_625.{u_1} : And
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y))))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
    @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y))))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
    @Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x))
  (@And.intro
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c))))
    (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y)
          (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_bounded α D E P y)))
    (@And.intro
      (And
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS))))
      (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
        (a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
            (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) a →
          ∀ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) b →
              ∃ (c : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
                And
                  (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D))
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet α D E P y) c)
                  (And
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      a c)
                    (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                      b c)))
      (@And.intro
        (And
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x))))
        (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
          {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)}
          (hS : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α D S hS))
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α E
              (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                  (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                S)
              (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded α D E P S hS)))
        (@And.intro
          (And
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S)))
          (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
            (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
            (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sInf α E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet α D E P x)
                (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty α D E P x)))
          (@And.intro
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E),
              Iff
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P) x)
                  y)
                (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
                  x
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E D
                    (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj α D E P) y)))
            (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              (P : @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair α D E)
              {S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)},
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α D S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α E
                  (@Set.image (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α D E
                      (@DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj α D E P))
                    S))
            @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.galois
            @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_bounded)
          @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_eq_sInf)
        @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.inj_sSup)
      @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.lowerSet_directed)
    @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.proj_eq_sSup)
  @DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair.upperSet_nonempty
end

end DomainTheory.NeighbourhoodSystems.Subsystem.ProjectionPair
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **A neighbourhood system is *finite*** when it has only finitely many neighbourhoods. -/
def NeighborhoodSystem.IsFinite {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  Finite {X : Set α // D.mem X}
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **The element-wise map of an injection `i` is an order embedding.** Given approximable maps
`i : D → E`, `j : E → D` with `j ∘ i = I_D`, the map `x ↦ i(x)` on elements is an order embedding
`|D| ↪o |E|`: monotone by `toElementMap_mono`, and order-reflecting because `j(·)` is a monotone
left inverse (`j(i(x)) = x`). Choice-free. -/
def projElementEmbedding {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D) (hji : j.comp i = idMap D) :
    D.Element ↪o E.Element :=
  OrderEmbedding.ofMapLEIff i.toElementMap (by
    have hround : ∀ x : D.Element, j.toElementMap (i.toElementMap x) = x := by
      intro x; rw [← toElementMap_comp, hji, toElementMap_idMap]
    intro a b
    constructor
    · intro h
      have hjm := toElementMap_mono j h
      rwa [hround a, hround b] at hjm
    · intro h
      exact toElementMap_mono i h)
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **`D ⊴ E` yields an order embedding `|D| ↪o |E|`.** Unfold `⊴` to an iso `|D| ≅o |D'|` onto a
subdomain `D' ◁ E`, turn `D' ◁ E` into Proposition 6.12's projection pair, and compose its
injection embedding with the iso. Choice-free. -/
theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **A finite system has a finite element domain.** A filter `x : |D|` is determined by which of
the (finitely many) neighbourhoods it contains, so `x ↦ {p | x.mem p.1}` injects `|D|` into the
finite powerset `Set {X // D.mem X}`. -/
theorem finite_element_of_isFinite {α : Type*} {D : NeighborhoodSystem α} (h : D.IsFinite) :
    Finite D.Element := by
  have : Finite {X : Set α // D.mem X} := h
  apply Finite.of_injective
    (β := Set {X : Set α // D.mem X}) (fun x => {p | x.mem p.1})
  intro x y hxy
  apply Element.ext
  intro X
  by_cases hX : D.mem X
  · have := Set.ext_iff.mp hxy ⟨X, hX⟩
    simpa using this
  · exact ⟨fun hmem => absurd (x.sub hmem) hX, fun hmem => absurd (y.sub hmem) hX⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Finite Cantor–Schröder–Bernstein (order version).** Mutual order embeddings between two
*finite* ordered types yield an order isomorphism. The embeddings are injective, so equal finite
cardinality forces `f` to be surjective; a surjective strictly-monotone map is an order iso. Uses
`Classical.choice` (via `Fintype`/surjection-section). -/
theorem orderIso_of_embeddings {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    [Finite P] [Finite Q] (f : P ↪o Q) (g : Q ↪o P) : Nonempty (P ≃o Q) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype P
  obtain ⟨_⟩ := nonempty_fintype Q
  have hcard : Fintype.card P = Fintype.card Q :=
    le_antisymm (Fintype.card_le_of_injective f f.injective)
      (Fintype.card_le_of_injective g g.injective)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, hcard⟩
  exact ⟨{ toEquiv := Equiv.ofBijective f hbij, map_rel_iff' := f.map_rel_iff' }⟩
end

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

end
end DomainTheory.NeighbourhoodSystems
end
