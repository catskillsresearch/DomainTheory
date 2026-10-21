/-ai
The element map of the approximable relation induced by a Scott-continuous map agrees with that map.

A token of the induced element comes from a finite input contained in the argument whose closure is sent into the value, and monotonicity of the Scott-continuous map puts the token in the value. In the other direction, algebraicity writes the argument as the directed supremum of its finite approximants, so the value is the directed supremum of their images. A token of the value therefore lies in the image of the closure of some consistent finite set contained in the argument, and that set is related to the singleton of the token.
ai-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]






namespace ApproximableMap

variable {A : InfoSys α} {B : InfoSys β}




/-- **Factoid 4.6 (←).** Scott-continuous maps recover as `toElement` of the induced
approximable relation. -/
theorem toElement_ofScottContinuous (g : ScottContinuous A B) (x : A.Element) :
    (ofScottContinuous g).toElement x = g.toFun x := by
  refine le_antisymm ?_ ?_
  · intro Y ⟨u, hu, ⟨huCon, _, hsub⟩⟩
    have : A.closure u huCon ≤ x := A.closure_le_element x huCon hu
    exact g.mono this (hsub (Finset.mem_coe.2 (Finset.mem_singleton_self Y)))
  · intro Y hY
    let S := A.finiteApproximants x
    have hne := A.nonempty_finiteApproximants x
    have hdir := A.directed_finiteApproximants x
    have hx : x = A.directedSup S hne hdir := A.eq_directedSup_finiteApproximants x
    have hdirImg := directed_image hdir g.toFun g.mono'
    have hneImg := nonempty_image hne g.toFun
    have hg : g.toFun x = B.directedSup (g.toFun '' S) hneImg hdirImg := by
      have h1 : g.toFun x = g.toFun (A.directedSup S hne hdir) := congrArg g.toFun hx
      have h2 : g.toFun (A.directedSup S hne hdir) =
          B.directedSup (g.toFun '' S) hneImg hdirImg :=
        g.map_directedSup S hne hdir
      exact h1.trans h2
    have hY' : Y ∈ (B.directedSup (g.toFun '' S) hneImg hdirImg).carrier := by
      rw [← hg]; exact hY
    have hY'' : Y ∈ B.familyUnionCarrier (g.toFun '' S) := by
      rwa [← B.directedSup_carrier_eq_union (g.toFun '' S) hneImg hdirImg]
    obtain ⟨z, hz, hYz⟩ := hY''
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨u, hu, huX, rfl⟩ := hy
    refine ⟨u, huX, ⟨hu, B.con_sing Y, ?_⟩⟩
    intro b hb
    have : b = Y := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact hYz

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
