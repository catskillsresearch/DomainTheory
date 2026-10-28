module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

section

def hOut : Str → Str
  | [] => []
  | b :: t => b :: false :: hOut t
end

section
@[simp] theorem hOut_nil : hOut [] = [] := rfl
end

section
@[simp] theorem hOut_cons (b : Bool) (t : Str) : hOut (b :: t) = b :: false :: hOut t := rfl
end

section

theorem hOut_append (σ t : Str) : hOut σ <+: hOut (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons b s ih =>
    simp only [List.cons_append, hOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, List.cons_append, hu]⟩
end

section

theorem hOut_mono {σ σ' : Str} (h : σ <+: σ') : hOut σ <+: hOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact hOut_append σ t
end

section

def kOut : Str → Str
  | [] => []
  | [_] => []
  | b :: _ :: t => b :: kOut t
end

section
@[simp] theorem kOut_nil : kOut [] = [] := rfl
end

section
@[simp] theorem kOut_single (b : Bool) : kOut [b] = [] := rfl
end

section
@[simp] theorem kOut_cons (b c : Bool) (t : Str) : kOut (b :: c :: t) = b :: kOut t := rfl
end

section

def hMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (hOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [hOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (hOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (hOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (hOut σ') ⊆ cone (hOut σ) := cone_subset_cone.mpr (hOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩
end

section

theorem kOut_append (σ t : Str) : kOut σ <+: kOut (σ ++ t) := by
  induction σ using kOut.induct with
  | case1 => simp
  | case2 _ => simp
  | case3 b c t' ih =>
    simp only [List.cons_append, kOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, hu]⟩
end

section

theorem kOut_mono {σ σ' : Str} (h : σ <+: σ') : kOut σ <+: kOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact kOut_append σ t
end

section

def kMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (kOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [kOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (kOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (kOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (kOut σ') ⊆ cone (kOut σ) := cone_subset_cone.mpr (kOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩
end

section

theorem kOut_hOut (σ : Str) : kOut (hOut σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b t ih => simp only [hOut_cons, kOut_cons, ih]
end

section

theorem kMap_comp_hMap : kMap.comp hMap = idMap B := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨σ, hXcone, _, hYsub⟩, τ, hYcone, hZmem, hZsub⟩
    refine ⟨⟨σ, hXcone⟩, hZmem, ?_⟩
    have hτ : τ <+: hOut σ := cone_subset_cone.mp (hYcone ▸ hYsub)
    have hτσ : kOut τ <+: σ := by have := kOut_mono hτ; rwa [kOut_hOut] at this
    calc X = cone σ := hXcone
      _ ⊆ cone (kOut τ) := cone_subset_cone.mpr hτσ
      _ ⊆ Z := hZsub
  · rintro ⟨⟨σ, hXcone⟩, hZmem, hXZ⟩
    refine ⟨cone (hOut σ), ⟨σ, hXcone, memB_cone (hOut σ), subset_rfl⟩, hOut σ, rfl, hZmem, ?_⟩
    rw [kOut_hOut, hXcone] at *
    exact hXZ
end

section

theorem toElementMap_hMap_cone (σ : Str) :
    hMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (hOut σ)) := by
  apply Element.ext
  intro Y
  rw [← hMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩
end

section

theorem toElementMap_kMap_cone (σ : Str) :
    kMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (kOut σ)) := by
  apply Element.ext
  intro Y
  rw [← kMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩
end

section

theorem hMap_not_surjective : ¬ Function.Surjective hMap.toElementMap := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (B.principal (memB_cone [false, true]))
  have hkhx : kMap.toElementMap (hMap.toElementMap x) = x := by
    rw [← toElementMap_comp, kMap_comp_hMap, toElementMap_idMap]
  rw [hx, toElementMap_kMap_cone] at hkhx
  rw [← hkhx, toElementMap_hMap_cone] at hx
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) hx)
  simp at hcone
end

section

theorem kMap_not_injective : ¬ Function.Injective kMap.toElementMap := by
  intro hinj
  have h1 : kMap.toElementMap (B.principal (memB_cone [false]))
      = kMap.toElementMap (B.principal (memB_cone [true])) := by
    rw [toElementMap_kMap_cone, toElementMap_kMap_cone]; rfl
  have h2 := hinj h1
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) h2)
  simp at hcone
end

section
set_option linter.unusedVariables false

theorem example_218 : And
  (And
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)))
  (Not
    (@Function.Injective
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap))) :=
  @And.intro
  (And
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)))
  (Not
    (@Function.Injective
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap)))
  (@And.intro
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B))
    DomainTheory.NeighbourhoodSystems.Exercise218.hMap_not_surjective
    DomainTheory.NeighbourhoodSystems.Exercise218.kMap_comp_hMap)
  DomainTheory.NeighbourhoodSystems.Exercise218.kMap_not_injective
end

end DomainTheory.NeighbourhoodSystems.Exercise218
