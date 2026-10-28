module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
public import Mathlib.Order.Hom.Basic
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

namespace ApproximableMap

section
variable {α β γ δ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

def ofIso (e : V₀.Element ≃o V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ _ : V₀.mem X, (e (V₀.principal ‹V₀.mem X›)).mem Y
  rel_dom := fun h => h.1
  rel_cod := fun h => (e _).sub h.2
  master_rel := ⟨V₀.master_mem, (e _).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (e (V₀.principal hX)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    have hle : V₀.principal hX ≤ V₀.principal hX' := (V₀.principal_le_iff hX hX').mpr hX'X
    have hmem : (e (V₀.principal hX')).mem Y := (e.monotone hle) Y hY
    exact (e (V₀.principal hX')).up_mem hmem hY' hYY'

theorem exists_principal_eq_apply_principal (e : V₀.Element ≃o V₁.Element)
    {X : Set α} (hX : V₀.mem X) :
    ∃ (Y : Set β) (hY : V₁.mem Y), e (V₀.principal hX) = V₁.principal hY := by

  set w : V₁.Element := e (V₀.principal hX) with hw
  set S : Set V₀.Element :=
    {z | ∃ (Y : Set β) (hY : V₁.mem Y), w.mem Y ∧ z = e.symm (V₁.principal hY)} with hS

  have hsymm_w : e.symm w = V₀.principal hX := by rw [hw, e.symm_apply_apply]

  have hprin_le_w : ∀ {Y : Set β} (hY : V₁.mem Y), w.mem Y → V₁.principal hY ≤ w :=
    fun hY hYw Z hZ => w.up_mem hYw hZ.1 hZ.2

  have hne : S.Nonempty :=
    ⟨e.symm (V₁.principal V₁.master_mem), V₁.master, V₁.master_mem, w.master_mem, rfl⟩

  have hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c := by
    rintro a ⟨Y, hY, hYw, rfl⟩ b ⟨Y', hY', hY'w, rfl⟩
    have hYY'w : w.mem (Y ∩ Y') := w.inter_mem hYw hY'w
    have hYY' : V₁.mem (Y ∩ Y') := w.sub hYY'w
    refine ⟨e.symm (V₁.principal hYY'), ⟨Y ∩ Y', hYY', hYY'w, rfl⟩, ?_, ?_⟩
    · exact e.symm.monotone ((V₁.principal_le_iff hY hYY').mpr Set.inter_subset_left)
    · exact e.symm.monotone ((V₁.principal_le_iff hY' hYY').mpr Set.inter_subset_right)

  set z : V₀.Element := V₀.sSupDirected S hne hdir with hz

  have hz_le : z ≤ V₀.principal hX := by
    apply V₀.sSupDirected_le
    rintro s ⟨Y, hY, hYw, rfl⟩
    have : e.symm (V₁.principal hY) ≤ e.symm w := e.symm.monotone (hprin_le_w hY hYw)
    rwa [hsymm_w] at this

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

  have hz_eq : z = V₀.principal hX := le_antisymm hz_le hX_le_z
  have hXz : z.mem X := hz_eq ▸ ⟨hX, subset_rfl⟩
  obtain ⟨s, ⟨Y, hY, hYw, rfl⟩, hXs⟩ := hXz

  refine ⟨Y, hY, ?_⟩
  have hprinX_le : V₀.principal hX ≤ e.symm (V₁.principal hY) :=
    fun Z hZ => (e.symm (V₁.principal hY)).up_mem hXs hZ.1 hZ.2
  have hw_le_prinY : w ≤ V₁.principal hY := by
    have := e.monotone hprinX_le
    rw [e.apply_symm_apply] at this
    rwa [← hw] at this
  exact le_antisymm hw_le_prinY (hprin_le_w hY hYw)

theorem toElementMap_ofIso (e : V₀.Element ≃o V₁.Element) (x : V₀.Element) :
    (ofIso e).toElementMap x = e x := by
  have hgxle : (ofIso e).toElementMap x ≤ e x := by
    rintro Y ⟨X, hXx, hX, hY⟩
    have hpx : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hXx hZ.1 hZ.2
    exact (e.monotone hpx) Y hY
  have key : x = e.symm ((ofIso e).toElementMap x) := by
    apply le_antisymm
    · intro X hXx
      have hX : V₀.mem X := x.sub hXx
      have hsub : e (V₀.principal hX) ≤ (ofIso e).toElementMap x :=
        fun Y hY => ⟨X, hXx, hX, hY⟩
      have hple : V₀.principal hX ≤ e.symm ((ofIso e).toElementMap x) := by
        have h := e.symm.monotone hsub
        rwa [e.symm_apply_apply] at h
      exact hple X ⟨hX, subset_rfl⟩
    · have h := e.symm.monotone hgxle
      rwa [e.symm_apply_apply] at h
  have h1 : e x = e (e.symm ((ofIso e).toElementMap x)) := congrArg e key
  rw [e.apply_symm_apply] at h1
  exact h1.symm

theorem exists_approximable_of_iso (e : V₀.Element ≃o V₁.Element) :
    ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x :=
  ⟨ofIso e, toElementMap_ofIso e⟩
end

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
