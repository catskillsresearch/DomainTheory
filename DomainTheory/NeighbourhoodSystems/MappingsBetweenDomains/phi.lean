module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ofIso
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal_le_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Neighbourhood corresponding to `X` under an order isomorphism of ideal elements. -/
noncomputable def phi (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) : Set β :=
  Classical.choose (exists_principal_eq_apply_principal e hX)

theorem phi_mem (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    V₁.mem (phi e hX) :=
  Classical.choose (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

theorem phi_spec (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    e (V₀.principal hX) = V₁.principal (phi_mem e hX) :=
  Classical.choose_spec (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

theorem phi_inter (e : V₀.Element ≃o V₁.Element) {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hXX' : V₀.mem (X ∩ X')) :
    phi e hXX' = phi e hX ∩ phi e hX' := by
  have hpX_le : V₀.principal hX ≤ V₀.principal hXX' :=
    (V₀.principal_le_iff hX hXX').mpr Set.inter_subset_left
  have hpX'_le : V₀.principal hX' ≤ V₀.principal hXX' :=
    (V₀.principal_le_iff hX' hXX').mpr Set.inter_subset_right
  have hleast : ∀ w : V₀.Element, V₀.principal hX ≤ w → V₀.principal hX' ≤ w →
      V₀.principal hXX' ≤ w := by
    intro w hXw hX'w Z hZ
    obtain ⟨hZmem, hsubZ⟩ := hZ
    have hwX : w.mem X := hXw X ⟨hX, subset_rfl⟩
    have hwX' : w.mem X' := hX'w X' ⟨hX', subset_rfl⟩
    exact w.up_mem (w.inter_mem hwX hwX') hZmem hsubZ
  have hqX : e (V₀.principal hX) = V₁.principal (phi_mem e hX) := phi_spec e hX
  have hqX' : e (V₀.principal hX') = V₁.principal (phi_mem e hX') := phi_spec e hX'
  have hqXX' : e (V₀.principal hXX') = V₁.principal (phi_mem e hXX') := phi_spec e hXX'
  have hsub1 : phi e hXX' ⊆ phi e hX := by
    have h : e (V₀.principal hX) ≤ e (V₀.principal hXX') := e.monotone hpX_le
    rw [hqX, hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hX) (phi_mem e hXX')).mp h
  have hsub1' : phi e hXX' ⊆ phi e hX' := by
    have h : e (V₀.principal hX') ≤ e (V₀.principal hXX') := e.monotone hpX'_le
    rw [hqX', hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hX') (phi_mem e hXX')).mp h
  have hsubInter : phi e hXX' ⊆ phi e hX ∩ phi e hX' := Set.subset_inter hsub1 hsub1'
  have hinter : V₁.mem (phi e hX ∩ phi e hX') :=
    V₁.inter_mem (phi_mem e hX) (phi_mem e hX') (phi_mem e hXX') hsubInter
  have hsub2 : phi e hX ∩ phi e hX' ⊆ phi e hXX' := by
    have hqXleI : e (V₀.principal hX) ≤ V₁.principal hinter := by
      rw [hqX]; exact (V₁.principal_le_iff (phi_mem e hX) hinter).mpr Set.inter_subset_left
    have hqX'leI : e (V₀.principal hX') ≤ V₁.principal hinter := by
      rw [hqX']; exact (V₁.principal_le_iff (phi_mem e hX') hinter).mpr Set.inter_subset_right
    have hpXleI : V₀.principal hX ≤ e.symm (V₁.principal hinter) := by
      have h := e.symm.monotone hqXleI; rwa [e.symm_apply_apply] at h
    have hpX'leI : V₀.principal hX' ≤ e.symm (V₁.principal hinter) := by
      have h := e.symm.monotone hqX'leI; rwa [e.symm_apply_apply] at h
    have hpXX'leI : V₀.principal hXX' ≤ e.symm (V₁.principal hinter) :=
      hleast _ hpXleI hpX'leI
    have h : e (V₀.principal hXX') ≤ V₁.principal hinter := by
      have h := e.monotone hpXX'leI; rwa [e.apply_symm_apply] at h
    rw [hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hXX') hinter).mp h
  exact Set.Subset.antisymm hsubInter hsub2

theorem rel_ofIso_iff (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    (ofIso e).rel X Y ↔ V₁.mem Y ∧ phi e hX ⊆ Y := by
  constructor
  · rintro ⟨_, hmem⟩
    have h : (e (V₀.principal hX)).mem Y := hmem
    rw [phi_spec e hX] at h
    exact h
  · intro h
    refine ⟨hX, ?_⟩
    rw [phi_spec e hX]
    exact h

end

end DomainTheory.NeighbourhoodSystems
