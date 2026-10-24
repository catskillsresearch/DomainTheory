module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.sSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ofIso
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ext
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.mem_toElementMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.idMap_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.comp_rel
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.toElementMap_idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.le_sSupDirected
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.sSupDirected_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.7 (Scott 1981, PRG-19) — finite elements go to finite elements.** A domain
isomorphism `e` carries the finite (principal) element `↑X` to a finite element `↑Y` of the other
domain. Following Scott: with `w = e(↑X)`, the set `S = {e⁻¹(↑Y) ∣ Y ∈ w}` is directed (intersections
of members of `w` give upper bounds), so its union `z = ⋃ S` is an element (`sSupDirected`). One shows
`z = ↑X` (each `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`, and conversely `w ⊑ e(z)` forces `↑X = e⁻¹(w) ⊑ z`); then
`X ∈ z` lands in some `e⁻¹(↑Y)`, giving `w ⊑ ↑Y`, while `↑Y ⊑ w` is automatic — so `w = ↑Y`. -/
theorem exists_principal_eq_apply_principal (e : V₀.Element ≃o V₁.Element)
    {X : Set α} (hX : V₀.mem X) :
    ∃ (Y : Set β) (hY : V₁.mem Y), e (V₀.principal hX) = V₁.principal hY := by
  -- `w = e(↑X)`, and the directed family `S` of inverse images of principals of members of `w`.
  set w : V₁.Element := e (V₀.principal hX) with hw
  set S : Set V₀.Element :=
    {z | ∃ (Y : Set β) (hY : V₁.mem Y), w.mem Y ∧ z = e.symm (V₁.principal hY)} with hS
  -- `e⁻¹(w) = ↑X`.
  have hsymm_w : e.symm w = V₀.principal hX := by rw [hw, e.symm_apply_apply]
  -- For `Y ∈ w`, `↑Y ⊑ w`.
  have hprin_le_w : ∀ {Y : Set β} (hY : V₁.mem Y), w.mem Y → V₁.principal hY ≤ w :=
    fun hY hYw Z hZ => w.up_mem hYw hZ.1 hZ.2
  -- `S` is non-empty (use `Y = Δ₁`).
  have hne : S.Nonempty :=
    ⟨e.symm (V₁.principal V₁.master_mem), V₁.master, V₁.master_mem, w.master_mem, rfl⟩
  -- `S` is directed: intersect the two members of `w`.
  have hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c := by
    rintro a ⟨Y, hY, hYw, rfl⟩ b ⟨Y', hY', hY'w, rfl⟩
    have hYY'w : w.mem (Y ∩ Y') := w.inter_mem hYw hY'w
    have hYY' : V₁.mem (Y ∩ Y') := w.sub hYY'w
    refine ⟨e.symm (V₁.principal hYY'), ⟨Y ∩ Y', hYY', hYY'w, rfl⟩, ?_, ?_⟩
    · exact e.symm.monotone ((V₁.principal_le_iff hY hYY').mpr Set.inter_subset_left)
    · exact e.symm.monotone ((V₁.principal_le_iff hY' hYY').mpr Set.inter_subset_right)
  -- The directed union `z = ⋃ S`.
  set z : V₀.Element := V₀.sSupDirected S hne hdir with hz
  -- `z ⊑ ↑X`: every member `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`.
  have hz_le : z ≤ V₀.principal hX := by
    apply V₀.sSupDirected_le
    rintro s ⟨Y, hY, hYw, rfl⟩
    have : e.symm (V₁.principal hY) ≤ e.symm w := e.symm.monotone (hprin_le_w hY hYw)
    rwa [hsymm_w] at this
  -- `↑X ⊑ z`: show `w ⊑ e(z)`, then `↑X = e⁻¹(w) ⊑ z`.
  have hw_le_ez : w ≤ e z := by
    intro Y hYw
    have hY : V₁.mem Y := w.sub hYw
    have hmem_S : e.symm (V₁.principal hY) ∈ S := ⟨Y, hY, hYw, rfl⟩
    have h1 : e.symm (V₁.principal hY) ≤ z := V₀.le_sSupDirected S hne hdir hmem_S
    have h2 : V₁.principal hY ≤ e z := by
      have := e.monotone h1
      rwa [e.apply_symm_apply] at this
    exact h2 Y ⟨hY, subset_rfl⟩
  have hX_le_z : V₀.principal hX ≤ z := by
    have : e.symm w ≤ e.symm (e z) := e.symm.monotone hw_le_ez
    rwa [hsymm_w, e.symm_apply_apply] at this
  -- Hence `z = ↑X`, so `X ∈ z` lands in some member `e⁻¹(↑Y)`.
  have hz_eq : z = V₀.principal hX := le_antisymm hz_le hX_le_z
  have hXz : z.mem X := hz_eq ▸ ⟨hX, subset_rfl⟩
  obtain ⟨s, ⟨Y, hY, hYw, rfl⟩, hXs⟩ := hXz
  -- `↑X ⊑ e⁻¹(↑Y)` (it contains `X`), so `w = e(↑X) ⊑ ↑Y`; with `↑Y ⊑ w` we get `w = ↑Y`.
  refine ⟨Y, hY, ?_⟩
  have hprinX_le : V₀.principal hX ≤ e.symm (V₁.principal hY) :=
    fun Z hZ => (e.symm (V₁.principal hY)).up_mem hXs hZ.1 hZ.2
  have hw_le_prinY : w ≤ V₁.principal hY := by
    have := e.monotone hprinX_le
    rw [e.apply_symm_apply] at this
    rwa [← hw] at this
  exact le_antisymm hw_le_prinY (hprin_le_w hY hYw)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
