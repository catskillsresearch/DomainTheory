module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.retraction
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cond
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sSupMaps

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Cond

section
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

theorem inMap₀_toElementMap_reaches_left {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₀.Element) :
    ∃ X, V₀.mem X ∧ ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₀ X) := by
  refine ⟨V₀.master, V₀.master_mem, V₀.master, v.master_mem, V₀.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inl ⟨V₀.master, V₀.master_mem, rfl⟩)

theorem inMap₁_toElementMap_reaches_right {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₁.Element) :
    ∃ Y, V₁.mem Y ∧ ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₁ Y) := by
  refine ⟨V₁.master, V₁.master_mem, V₁.master, v.master_mem, V₁.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inr ⟨V₁.master, V₁.master_mem, rfl⟩)

theorem not_sum_reaches_both {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
    {w : (sum V₀ V₁ h₀ h₁).Element} (hL : ∃ X, V₀.mem X ∧ w.mem (inj₀ X))
    (hR : ∃ Y, V₁.mem Y ∧ w.mem (inj₁ Y)) : False := by
  obtain ⟨X, _, hX⟩ := hL
  obtain ⟨Y, _, hY⟩ := hR
  have h := w.inter_mem hX hY
  rw [inj₀_inter_inj₁] at h
  exact not_sum_mem_empty (w.sub h)

theorem toElementMap_idem_of_isRetraction {a : ApproximableMap E E} (ha : Retraction a)
    (x : E.Element) : a.toElementMap (a.toElementMap x) = a.toElementMap x := by
  rw [← toElementMap_comp, ha.out]

theorem toElementMap_le_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) (x : E.Element) : i.toElementMap (j.toElementMap x) ≤ x := by
  have h := (le_iff_toElementMap_le.mp hij) x
  rwa [toElementMap_comp, toElementMap_idMap] at h

theorem toElementMap_le_self_of_le_idMap {a : ApproximableMap E E} (ha : a ≤ idMap E)
    (x : E.Element) : a.toElementMap x ≤ x := by
  have h := (le_iff_toElementMap_le.mp ha) x
  rwa [toElementMap_idMap] at h

theorem toElementMap_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) (v : D.Element) : j.toElementMap (i.toElementMap v) = v := by
  rw [← toElementMap_comp, hji, toElementMap_idMap]

end

end DomainTheory.NeighbourhoodSystems
