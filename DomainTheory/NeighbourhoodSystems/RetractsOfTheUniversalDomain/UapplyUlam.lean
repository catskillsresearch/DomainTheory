module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

noncomputable def Uapply (u x : U.Element) : U.Element :=
  (evalMap U U).toElementMap (pair (jArrow.toElementMap u) x)

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

noncomputable def Ulam (f : ApproximableMap U U) : U.Element :=
  iArrow.toElementMap (toFilter f)

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

def translateAbs (a b body : ApproximableMap E E) : ApproximableMap E E :=
  b.comp (body.comp a)
end

theorem Uapply_Ulam (f : ApproximableMap U U) (x : U.Element) :
    Uapply (Ulam f) x = f.toElementMap x := by
  have hround : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv U U).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  unfold Uapply Ulam
  have h1 : jArrow.toElementMap (iArrow.toElementMap (toFilter f))
      = (jArrow.comp iArrow).toElementMap (toFilter f) :=
    (toElementMap_comp jArrow iArrow (toFilter f)).symm
  rw [h1, jArrow_comp_iArrow, toElementMap_idMap, evalMap_apply, hround]

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

theorem translateAbs_idMap {a b : ApproximableMap E E} : translateAbs a b (idMap E) = b.comp a := by
  unfold translateAbs
  rw [idMap_comp]
end

set_option linter.unusedVariables false

theorem example_826.{u} : ∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
    (@DomainTheory.NeighbourhoodSystems.translateAbs α E a b
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α E))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α E E E b a) :=
  @DomainTheory.NeighbourhoodSystems.translateAbs_idMap

section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

theorem translateAbs_sandwich {a b body : ApproximableMap E E}
    (ha : Retraction a) (hb : Retraction b) :
    b.comp ((translateAbs a b body).comp a) = translateAbs a b body := by
  show b.comp ((b.comp (body.comp a)).comp a) = b.comp (body.comp a)
  rw [comp_assoc b (body.comp a) a, comp_assoc body a a, ha.out, ← comp_assoc b b (body.comp a), hb.out]

theorem translateApp_hasType {a b f : ApproximableMap E E} (hsandwich : b.comp (f.comp a) = f)
    {x : E.Element} (hx : a.toElementMap x = x) :
    b.toElementMap (f.toElementMap x) = f.toElementMap x := by
  conv_rhs => rw [← hsandwich, toElementMap_comp, toElementMap_comp, hx]

end

end DomainTheory.NeighbourhoodSystems
