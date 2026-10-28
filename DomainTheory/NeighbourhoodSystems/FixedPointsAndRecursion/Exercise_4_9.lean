module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem_4_2
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_12

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
section
variable {α : Type*}

def bigPsi (V : NeighborhoodSystem α) :
    ApproximableMap (funSpace (funSpace V V) V) (funSpace (funSpace V V) V) :=
  curry ((evalMap V V).comp
    (paired (proj₁ (funSpace (funSpace V V) V) (funSpace V V)) (evalMap (funSpace V V) V)))

theorem bigPsi_apply (V : NeighborhoodSystem α)
    (θ : (funSpace (funSpace V V) V).Element) (f : (funSpace V V).Element) :
    (toApproxMap ((bigPsi V).toElementMap θ)).toElementMap f
      = (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f) := by
  rw [bigPsi, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply, evalMap_apply]

theorem toApproxMap_toFilter_fixMap (V : NeighborhoodSystem α) :
    toApproxMap (toFilter (fixMap V)) = fixMap V := by
  have he := (funSpaceEquiv (funSpace V V) V).apply_symm_apply (fixMap V)
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he

theorem bigPsi_fix (V : NeighborhoodSystem α) :
    (bigPsi V).toElementMap (toFilter (fixMap V)) = toFilter (fixMap V) := by
  apply (funSpaceEquiv (funSpace V V) V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro f
  rw [bigPsi_apply, toApproxMap_toFilter_fixMap, fixMap_toElementMap, toElementMap_fixElement]

theorem bigPsi_least (V : NeighborhoodSystem α) (θ : (funSpace (funSpace V V) V).Element)
    (hθ : (bigPsi V).toElementMap θ ≤ θ) : toFilter (fixMap V) ≤ θ := by

  have hθ' : toApproxMap ((bigPsi V).toElementMap θ) ≤ toApproxMap θ := by
    rw [← funSpaceEquiv_apply, ← funSpaceEquiv_apply]
    exact (funSpaceEquiv (funSpace V V) V).monotone hθ
  have hpre : ∀ f, (toApproxMap f).toElementMap ((toApproxMap θ).toElementMap f)
      ≤ (toApproxMap θ).toElementMap f := by
    intro f
    have h := (le_iff_toElementMap_le.mp hθ') f
    rwa [bigPsi_apply] at h

  apply (funSpaceEquiv (funSpace V V) V).le_iff_le.mp
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toFilter_fixMap, le_iff_toElementMap_le]
  intro f
  rw [fixMap_toElementMap]
  exact fixElement_le_of_toElementMap_le (toApproxMap f) (hpre f)

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

end DomainTheory.NeighbourhoodSystems
end
