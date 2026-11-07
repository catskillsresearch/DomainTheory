module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.fixMap
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.SeqDom
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap BitDom

section

def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})
end

section
theorem memC_cone (σ : Str) : memC (cone σ) := Or.inl ⟨σ, rfl⟩
end

section
theorem memC_singleton (σ : Str) : memC ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩
end

section

theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩
end

section

theorem prepend_singleton (σ τ : Str) : prepend σ {τ} = {σ ++ τ} := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨τ, rfl, rfl⟩
end

section

theorem singleton_subset_cone {σ τ : Str} : ({τ} : Set Str) ⊆ cone σ ↔ σ <+: τ := by
  rw [Set.singleton_subset_iff, cone.mem]
end

section

theorem singleton_cone_nd (σ τ : Str) :
    ({τ} : Set Str) ⊆ cone σ ∨ cone σ ⊆ {τ} ∨ ({τ} : Set Str) ∩ cone σ = ∅ := by
  by_cases h : σ <+: τ
  · exact Or.inl (singleton_subset_cone.mpr h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, cone.mem, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hτ
    exact h hτ
end

section

theorem nestedOrDisjoint : NestedOrDisjoint memC := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact cone.trichotomy σ τ
  · rcases singleton_cone_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_cone_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2
end

end DomainTheory.NeighbourhoodSystems.SeqDom

section
namespace DomainTheory.NeighbourhoodSystems.SeqDom
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap BitDom
section

abbrev C : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memC Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], cone.nil.symm⟩) nestedOrDisjoint
    (fun _ => Set.subset_univ _)
end

section
@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl
end

section
@[simp] theorem C_master : C.master = (Set.univ : Set Str) := rfl
end

section

theorem memC_prepend (σ : Str) {X : Set Str} (hX : memC X) : memC (prepend σ X) := by
  rcases hX with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact Or.inl ⟨σ ++ ρ, prepend_cone σ ρ⟩
  · exact Or.inr ⟨σ ++ ρ, prepend_singleton σ ρ⟩
end

section

def consMap (b : Bool) : ApproximableMap C C where
  rel X Y := memC X ∧ memC Y ∧ prepend [b] X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨Or.inl ⟨[], cone.nil.symm⟩, Or.inl ⟨[], cone.nil.symm⟩, ?_⟩
    exact Set.subset_univ _
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hsubInter : prepend [b] X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    have hZ : memC (prepend [b] X) := memC_prepend [b] hX
    exact ⟨hX, C.inter_mem hY hY' hZ hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (prepend_mono [b] hX'X).trans (hsub.trans hYY')⟩
end

section

def altElt : C.Element := ((consMap false).comp (consMap true)).fixElement
end

section

def strBot (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_cone σ))
end

section

def strElem (σ : Str) : C.Element := C.principal (C_mem.mpr (memC_singleton σ))
end

section

theorem altElt_eq : (consMap false).toElementMap ((consMap true).toElementMap altElt) = altElt := by
  have h := toElementMap_fixElement ((consMap false).comp (consMap true))
  rwa [toElementMap_comp] at h
end

section

theorem consMap_strBot (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strBot σ) = strBot (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] (cone σ) ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_cone] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, memC_cone σ, hY, ?_⟩
    rw [prepend_cone]; exact hsub
end

section

theorem consMap_strElem (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strElem σ) = strElem (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] {σ} ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, memC_singleton σ, hY, ?_⟩
    rw [prepend_singleton]; exact hsub
end

section

theorem prepend_subset_self : True := trivial
end

end DomainTheory.NeighbourhoodSystems.SeqDom
