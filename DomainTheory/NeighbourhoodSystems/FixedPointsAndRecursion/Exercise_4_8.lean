module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_7

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*} {V : NeighborhoodSystem α}
namespace ApproximableMap

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

theorem fix_induction_eq (f a b : ApproximableMap V V)
    (hbot : a.toElementMap V.bot = b.toElementMap V.bot)
    (hfa : f.comp a = a.comp f) (hfb : f.comp b = b.comp f) :
    a.toElementMap f.fixElement = b.toElementMap f.fixElement := by

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

end DomainTheory.NeighbourhoodSystems
end
