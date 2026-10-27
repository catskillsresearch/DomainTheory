module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_1

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α : Type*} {D E : NeighborhoodSystem α}
namespace Subsystem
/- concordance: source L4771 PROPOSITION 8.2 retractions from subdomains -/
/-- **Proposition 8.2 (Scott 1981, PRG-19), packaged.** `D ◁ E` induces a retraction `a` on `E`
whose fixed-point set is (order-isomorphic to) `|D|`. -/
theorem retraction_of_subsystem (h : D ◁ E) :
    Retraction (retractionOfSubsystem h) ∧
      Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y}) :=
  ⟨isRetraction_retractionOfSubsystem h, ⟨elementIso h⟩⟩

end Subsystem
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Subsystem
set_option linter.unusedVariables false

theorem theorem_82.{u_1} : And
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @DomainTheory.NeighbourhoodSystems.Retraction α E
      (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    And
      (@DomainTheory.NeighbourhoodSystems.Retraction α E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
      (Nonempty
        (@OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
          (@Subtype (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
          (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y)))) :=
  @And.intro
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    @DomainTheory.NeighbourhoodSystems.Retraction α E
      (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
  (∀ {α : Type u_1} {D E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (h : @DomainTheory.NeighbourhoodSystems.Subsystem α D E),
    And
      (@DomainTheory.NeighbourhoodSystems.Retraction α E
        (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h))
      (Nonempty
        (@OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
          (@Subtype (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α D)))
          (@Subtype.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α E)))
            fun (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E) =>
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α E)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α E E
                (@DomainTheory.NeighbourhoodSystems.Subsystem.retractionOfSubsystem α D E h) y)
              y))))
  @DomainTheory.NeighbourhoodSystems.Subsystem.isRetraction_retractionOfSubsystem
  @DomainTheory.NeighbourhoodSystems.Subsystem.retraction_of_subsystem

end DomainTheory.NeighbourhoodSystems.Subsystem
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {D E : NeighborhoodSystem α}

/-- **Definition 8.3, second clause (Scott 1981, PRG-19).** A retraction `a : E → E` is *finitary*
iff its fixed-point set `{y ∈ |E| ∣ a(y) = y}` — ordered by the inherited inclusion `⊑` — is
isomorphic to (the element poset of) some neighbourhood system. -/
def IsFinitary (a : ApproximableMap E E) : Prop :=
  ∃ (β : Type u) (F : NeighborhoodSystem β),
    Nonempty ({y : E.Element // a.toElementMap y = y} ≃o F.Element)

end
end DomainTheory.NeighbourhoodSystems
