module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal_injective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.HMap
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem BitDom ApproximableMap

def hOut : Str → Str
  | [] => []
  | b :: t => b :: false :: hOut t

@[simp] theorem hOut_nil : hOut [] = [] := rfl

@[simp] theorem hOut_cons (b : Bool) (t : Str) : hOut (b :: t) = b :: false :: hOut t := rfl

theorem hOut_append (σ t : Str) : hOut σ <+: hOut (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons b s ih =>
    simp only [List.cons_append, hOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, List.cons_append, hu]⟩

theorem hOut_mono {σ σ' : Str} (h : σ <+: σ') : hOut σ <+: hOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact hOut_append σ t

def kOut : Str → Str
  | [] => []
  | [_] => []
  | b :: _ :: t => b :: kOut t

@[simp] theorem kOut_nil : kOut [] = [] := rfl

@[simp] theorem kOut_single (b : Bool) : kOut [b] = [] := rfl

@[simp] theorem kOut_cons (b c : Bool) (t : Str) : kOut (b :: c :: t) = b :: kOut t := rfl

/-- Approximable map inserting a zero after each bit. -/
def hMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (hOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone.nil.symm, B.master_mem, ?_⟩
    rw [hOut_nil, B_master, cone.nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone.injective (hX ▸ hX')
    subst hσ
    have hsub : cone (hOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (hOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone.subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (hOut σ') ⊆ cone (hOut σ) := cone.subset_cone.mpr (hOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

theorem kOut_append (σ t : Str) : kOut σ <+: kOut (σ ++ t) := by
  induction σ using kOut.induct with
  | case1 => simp
  | case2 _ => simp
  | case3 b c t' ih =>
    simp only [List.cons_append, kOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, hu]⟩

theorem kOut_mono {σ σ' : Str} (h : σ <+: σ') : kOut σ <+: kOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact kOut_append σ t

/-- Left inverse (on the image of `hMap`) that drops every other bit. -/
def kMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (kOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone.nil.symm, B.master_mem, ?_⟩
    rw [kOut_nil, B_master, cone.nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone.injective (hX ▸ hX')
    subst hσ
    have hsub : cone (kOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (kOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone.subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (kOut σ') ⊆ cone (kOut σ) := cone.subset_cone.mpr (kOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

theorem kOut_hOut (σ : Str) : kOut (hOut σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b t ih => simp only [hOut_cons, kOut_cons, ih]

theorem kMap_comp_hMap : kMap.comp hMap = idMap B := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨σ, hXcone, _, hYsub⟩, τ, hYcone, hZmem, hZsub⟩
    refine ⟨⟨σ, hXcone⟩, hZmem, ?_⟩
    have hτ : τ <+: hOut σ := cone.subset_cone.mp (hYcone ▸ hYsub)
    have hτσ : kOut τ <+: σ := by have := kOut_mono hτ; rwa [kOut_hOut] at this
    calc X = cone σ := hXcone
      _ ⊆ cone (kOut τ) := cone.subset_cone.mpr hτσ
      _ ⊆ Z := hZsub
  · rintro ⟨⟨σ, hXcone⟩, hZmem, hXZ⟩
    refine ⟨cone (hOut σ), ⟨σ, hXcone, memB_cone (hOut σ), subset_rfl⟩, hOut σ, rfl, hZmem, ?_⟩
    rw [kOut_hOut, hXcone] at *
    exact hXZ

theorem toElementMap_hMap_cone (σ : Str) :
    hMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (hOut σ)) := by
  apply Element.ext
  intro Y
  rw [← hMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone.injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

theorem toElementMap_kMap_cone (σ : Str) :
    kMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (kOut σ)) := by
  apply Element.ext
  intro Y
  rw [← kMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone.injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

theorem hMap_not_surjective : ¬ Function.Surjective hMap.toElementMap := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (B.principal (memB_cone [false, true]))
  have hkhx : kMap.toElementMap (hMap.toElementMap x) = x := by
    rw [← toElementMap_comp, kMap_comp_hMap, toElementMap_idMap]
  rw [hx, toElementMap_kMap_cone] at hkhx
  rw [← hkhx, toElementMap_hMap_cone] at hx
  have hcone := cone.injective (B.principal_injective (memB_cone _) (memB_cone _) hx)
  simp at hcone

theorem kMap_not_injective : ¬ Function.Injective kMap.toElementMap := by
  intro hinj
  have h1 : kMap.toElementMap (B.principal (memB_cone [false]))
      = kMap.toElementMap (B.principal (memB_cone [true])) := by
    rw [toElementMap_kMap_cone, toElementMap_kMap_cone]; rfl
  have h2 := hinj h1
  have hcone := cone.injective (B.principal_injective (memB_cone _) (memB_cone _) h2)
  simp at hcone

end DomainTheory.NeighbourhoodSystems.HMap
