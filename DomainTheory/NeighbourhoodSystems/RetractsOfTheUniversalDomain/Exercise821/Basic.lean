module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharpInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharp_fixedNbhd_elementIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.grel_inSharp_pairSharp_imp_idMap_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.idMap_rel_imp_grel_inSharp_pairSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.gMap_inSharp_pairSharp_eq_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.pair_principal_eq_principal_prodNbhd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.inSharp_principal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.pairSharp_principal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.gMap_eq_of_satisfies
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.jSharp_comp_iSharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.aSharp_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_id
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_comp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.dsharpMap_self_eq_aSharpInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.JSharpComb_comp_ISharpComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821.ISharpComb_comp_JSharpComb

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_in
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_pair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_strict
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Exercise 8.21(b)(2), general form.** If `a : D → D` is a retraction, so is the recursive
extension `gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD` of `a`'s tree algebra (`aSharpInner a`
specializes this at `D := U`). Applies `gMap_eq_of_satisfies` to `k := g.comp g` (`g` the catamorphism
itself): both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to the
corresponding equation for `g` composed with `a`'s own idempotence. -/
theorem gMap_selfComp_eq_of_isRetraction {a : ApproximableMap D D} (ha : Retraction a) :
    (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD).comp
        (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD)
      = gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD := by
  set u : ApproximableMap D (Dsharp D hD) := (inSharpMap hD).comp a with hu_def
  set v : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) :=
    pairSharpMap hD with hv_def
  set g : ApproximableMap (Dsharp D hD) (Dsharp D hD) := gMap u v hD with hg_def
  have hu_eq : ∀ y : D.Element, u.toElementMap y = inSharp D hD (a.toElementMap y) := by
    intro y; rw [hu_def, toElementMap_comp, inSharpMap_toElementMap]
  show g.comp g = g
  apply gMap_eq_of_satisfies
  · rw [hg_def]; exact isStrict_comp (gMap_strict hD) (gMap_strict hD)
  · intro x
    have e1 : g.toElementMap (inSharp D hD x) = u.toElementMap x := by
      rw [hg_def]; exact gMap_in hD x
    have e2 : g.toElementMap (u.toElementMap x) = u.toElementMap (a.toElementMap x) := by
      rw [hu_eq x, hg_def]; exact gMap_in hD (a.toElementMap x)
    calc (g.comp g).toElementMap (inSharp D hD x)
        = g.toElementMap (g.toElementMap (inSharp D hD x)) := toElementMap_comp _ _ _
      _ = g.toElementMap (u.toElementMap x) := by rw [e1]
      _ = u.toElementMap (a.toElementMap x) := e2
      _ = inSharp D hD (a.toElementMap (a.toElementMap x)) := hu_eq _
      _ = inSharp D hD (a.toElementMap x) := by rw [toElementMap_idem_of_isRetraction ha]
      _ = u.toElementMap x := (hu_eq x).symm
  · intro y z
    have e1 : g.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (g.toElementMap y) (g.toElementMap z)) := by
      rw [hg_def]; exact gMap_pair hD y z
    have e2 : v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))
        = pairSharp D hD (g.toElementMap y) (g.toElementMap z) := by
      rw [hv_def]; exact pairSharpMap_toElementMap hD _ _
    have e3 : g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z))
        = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := by
      rw [hg_def]; exact gMap_pair hD _ _
    calc (g.comp g).toElementMap (pairSharp D hD y z)
        = g.toElementMap (g.toElementMap (pairSharp D hD y z)) := toElementMap_comp _ _ _
      _ = g.toElementMap (v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))) := by
          rw [e1]
      _ = g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z)) := by rw [e2]
      _ = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := e3
      _ = v.toElementMap (pair ((g.comp g).toElementMap y) ((g.comp g).toElementMap z)) := by
          rw [toElementMap_comp, toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
