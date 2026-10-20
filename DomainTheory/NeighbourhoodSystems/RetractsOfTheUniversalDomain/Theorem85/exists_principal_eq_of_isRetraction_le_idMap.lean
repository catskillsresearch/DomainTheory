module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.principal_isCompactElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.eq_principal_of_isCompactElt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.toElementMap_idem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.e_apply_iSupDirected_fixed

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}






section HardDirection

variable {a : ApproximableMap E E}



variable {β : Type u} {F : NeighborhoodSystem β} (e : FixSet a ≃o F.Element)




/-- **Scott's compactness-reflection fact.** If `e.symm(w')` is a *principal* (finite) element of
`F`, then `e.symm(w')`'s image `.1` in `E` need not be principal; the content here is the converse
direction: **pulling a genuinely principal element of `F` back through `e.symm` always lands on a
principal element of `E`.** The key step lifts compactness across the retraction: any `E`-directed
family bounding `(e.symm(↑Y)).1` from above can be replaced (applying the continuous, idempotent
`a`) by an `a`-fixed directed family with the same sup-relationship, and `a ≤ idMap E` (`a` is a
*projection*, not just a retraction) is exactly what lets the bound transfer back down. -/
theorem exists_principal_eq_of_isRetraction_le_idMap (ha_ret : IsRetraction a)
    (ha_proj : a ≤ idMap E) {Y : Set β} (hY : F.mem Y) :
    ∃ (X : Set α) (hX : E.mem X), (e.symm (F.principal hY)).1 = E.principal hX := by
  apply eq_principal_of_isCompactElt
  intro I _ d hdir hle
  set d2 : I → E.Element := fun i => a.toElementMap (d i) with hd2
  have hdir2 : ∀ i j, ∃ k, d2 i ≤ d2 k ∧ d2 j ≤ d2 k := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, a.toElementMap_mono hik, a.toElementMap_mono hjk⟩
  have hfix2 : ∀ i, a.toElementMap (d2 i) = d2 i := fun i => toElementMap_idem ha_ret (d i)
  have hle2 : (e.symm (F.principal hY)).1 ≤ iSupDirected d2 hdir2 := by
    calc (e.symm (F.principal hY)).1 = a.toElementMap (e.symm (F.principal hY)).1 :=
          (e.symm (F.principal hY)).2.symm
      _ ≤ a.toElementMap (iSupDirected d hdir) := a.toElementMap_mono hle
      _ = iSupDirected d2 hdir2 := toElementMap_iSupDirected a d hdir
  have hSfix2 : a.toElementMap (iSupDirected d2 hdir2) = iSupDirected d2 hdir2 :=
    toElementMap_iSupDirected_fixed d2 hdir2 hfix2
  have hdir2' : ∀ i j : I, ∃ k, e ⟨d2 i, hfix2 i⟩ ≤ e ⟨d2 k, hfix2 k⟩ ∧
      e ⟨d2 j, hfix2 j⟩ ≤ e ⟨d2 k, hfix2 k⟩ := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hdir2 i j
    exact ⟨k, e.monotone hik, e.monotone hjk⟩
  have hle3 : F.principal hY ≤ iSupDirected (fun i => e ⟨d2 i, hfix2 i⟩) hdir2' := by
    have h1 : e ⟨(e.symm (F.principal hY)).1, (e.symm (F.principal hY)).2⟩ ≤
        e ⟨iSupDirected d2 hdir2, hSfix2⟩ := e.monotone hle2
    rwa [Subtype.coe_eta, e.apply_symm_apply,
      e_apply_iSupDirected_fixed e d2 hdir2 hfix2 hSfix2 hdir2'] at h1
  obtain ⟨i0, hi0⟩ := principal_isCompactElt hY _ _ hle3
  have hi0' : e.symm (F.principal hY) ≤ ⟨d2 i0, hfix2 i0⟩ := by
    have := e.symm.monotone hi0
    rwa [e.symm_apply_apply] at this
  have hfinal : (e.symm (F.principal hY)).1 ≤ d2 i0 := hi0'
  have hd2le : d2 i0 ≤ d i0 := by
    have := (le_iff_toElementMap_le.mp ha_proj) (d i0)
    rwa [toElementMap_idMap] at this
  exact ⟨i0, hfinal.trans hd2le⟩

end HardDirection
end DomainTheory.NeighbourhoodSystems
