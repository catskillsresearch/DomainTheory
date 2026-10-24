module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_7
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/- concordance: source L845 EXERCISE 2.14 isomorphisms of neighbourhoods -/
/-- **Exercise 2.14 — the correspondence `φ`.** For a domain isomorphism `e` and `X ∈ 𝒟₀`, `φ(X)` is
the neighbourhood with `e(↑X) = ↑φ(X)` provided by Theorem 2.7. -/
noncomputable def phi (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) : Set β :=
  Classical.choose (exists_principal_eq_apply_principal e hX)
end

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- `φ(X) ∈ 𝒟₁`. -/
theorem phi_mem (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    V₁.mem (phi e hX) :=
  Classical.choose (Classical.choose_spec (exists_principal_eq_apply_principal e hX))
end

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 2.7 defining equation: `e(↑X) = ↑φ(X)`.** -/
theorem phi_spec (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    e (V₀.principal hX) = V₁.principal (phi_mem e hX) :=
  Classical.choose_spec (Classical.choose_spec (exists_principal_eq_apply_principal e hX))
end

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.14 — `φ` preserves consistent intersections.** If `X, X'` are consistent
(`X ∩ X' ∈ 𝒟₀`), then `φ(X ∩ X') = φ(X) ∩ φ(X')`.

`↑(X ∩ X')` is the join of `↑X, ↑X'` in `|𝒟₀|` (the order is inclusion-reversed). `e`/`e.symm`
preserve this least upper bound, and the join of the consistent principals `↑φ(X), ↑φ(X')` is
`↑(φ(X) ∩ φ(X'))`. -/
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
end

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.14 — the approximable mapping of `e` is `φ(X) ⊆ Y`.** For `X ∈ 𝒟₀`,
`(ofIso e).rel X Y ↔ Y ∈ 𝒟₁ ∧ φ(X) ⊆ Y`. (Immediate from `phi_spec` and `mem_principal`.) -/
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

section
set_option linter.unusedVariables false

theorem example_214.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X X' : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X)
    (hX' : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X')
    (hXX' :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Inter.inter (Set α) (@Set.instInter α) X X')),
    @Eq (Set β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e (@Inter.inter (Set α) (@Set.instInter α) X X') hXX')
      (@Inter.inter (Set β) (@Set.instInter β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX)
        (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X' hX')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X) {Y : Set β},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β V₀ V₁ e) X Y)
      (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y)
        (@LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX) Y))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X X' : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X)
    (hX' : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X')
    (hXX' :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Inter.inter (Set α) (@Set.instInter α) X X')),
    @Eq (Set β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e (@Inter.inter (Set α) (@Set.instInter α) X X') hXX')
      (@Inter.inter (Set β) (@Set.instInter β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX)
        (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X' hX')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X) {Y : Set β},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β V₀ V₁ e) X Y)
      (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y)
        (@LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX) Y)))
  @DomainTheory.NeighbourhoodSystems.phi_inter @DomainTheory.NeighbourhoodSystems.rel_ofIso_iff
end

end DomainTheory.NeighbourhoodSystems
