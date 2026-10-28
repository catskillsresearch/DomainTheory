module

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

theorem inj_bounded (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    E.Bounded (P.inj.toElementMap '' S) := by
  obtain ⟨b, hb⟩ := hS
  refine ⟨P.inj.toElementMap b, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact P.inj.toElementMap_mono (hb s hs)

theorem inj_proj_apply_le (P : ProjectionPair D E) (y : E.Element) :
    P.inj.toElementMap (P.proj.toElementMap y) ≤ y := by
  have h := (le_iff_toElementMap_le.mp P.inj_comp_proj_le) y
  rwa [toElementMap_comp, toElementMap_idMap] at h

theorem proj_inj_apply (P : ProjectionPair D E) (x : D.Element) :
    P.proj.toElementMap (P.inj.toElementMap x) = x := by
  rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]

theorem galois (P : ProjectionPair D E) (x : D.Element) (y : E.Element) :
    P.inj.toElementMap x ≤ y ↔ x ≤ P.proj.toElementMap y := by
  constructor
  · intro hxy
    have := P.proj.toElementMap_mono hxy
    rwa [P.proj_inj_apply x] at this
  · intro hxy
    exact (P.inj.toElementMap_mono hxy).trans (P.inj_proj_apply_le y)

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

theorem lowerSet_bounded (P : ProjectionPair D E) (y : E.Element) :
    D.Bounded (P.lowerSet y) :=
  ⟨P.proj.toElementMap y, fun _ hx => (P.galois _ y).mp hx⟩

theorem lowerSet_directed (P : ProjectionPair D E) (y : E.Element) :
    ∀ a ∈ P.lowerSet y, ∀ b ∈ P.lowerSet y,
      ∃ c ∈ P.lowerSet y, a ≤ c ∧ b ≤ c := by
  intro a ha b hb
  exact ⟨P.proj.toElementMap y, P.inj_proj_apply_le y,
    (P.galois a y).mp ha, (P.galois b y).mp hb⟩

theorem proj_eq_sSup (P : ProjectionPair D E) (y : E.Element) :
    P.proj.toElementMap y = D.sSup (P.lowerSet y) (P.lowerSet_bounded y) := by
  apply le_antisymm
  · exact D.le_sSup _ (P.lowerSet_bounded y) (P.inj_proj_apply_le y)
  · exact D.sSup_le _ (P.lowerSet_bounded y) fun x hx => (P.galois x y).mp hx

theorem upperSet_nonempty (P : ProjectionPair D E) (x : D.Element) :
    (P.upperSet x).Nonempty :=
  ⟨P.inj.toElementMap x, by rw [mem_upperSet, P.proj_inj_apply x]⟩

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

def NeighborhoodSystem.IsFinite {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  Finite {X : Set α // D.mem X}

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

theorem Trianglelefteq.elementEmbedding (h : D ⊴ E) :
    Nonempty (D.Element ↪o E.Element) := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  exact ⟨e.toOrderEmbedding.trans
    (projElementEmbedding hsub.inj hsub.proj hsub.proj_comp_inj)⟩

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
end DomainTheory.NeighbourhoodSystems
end
