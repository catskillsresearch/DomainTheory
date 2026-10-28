module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_19
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Examples_1_2_1_5_revisited
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
@[expose] public section

section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem cone_not_subset_singleton (σ τ : Str) : ¬ cone σ ⊆ ({τ} : Set Str) := by
  intro h
  have h1 : σ ∈ ({τ} : Set Str) := h (mem_cone.mpr List.prefix_rfl)
  have h2 : (σ ++ [false]) ∈ ({τ} : Set Str) := h (mem_cone.mpr (List.prefix_append σ [false]))
  rw [Set.mem_singleton_iff] at h1 h2
  rw [← h1] at h2
  have hlen := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end DomainTheory.NeighbourhoodSystems.Exercise221
end

namespace DomainTheory.NeighbourhoodSystems.Exercise221
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section

theorem cone_ne_singleton (σ τ : Str) : cone σ ≠ ({τ} : Set Str) := by
  intro h
  refine cone_not_subset_singleton σ τ ?_
  intro x hx
  rw [← h]; exact hx
end

section

theorem cone_singleton_nd (σ τ : Str) :
    cone σ ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ cone σ ∨ cone σ ∩ ({τ} : Set Str) = ∅ :=
  if h : σ <+: τ then
    Or.inr (Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h)))
  else
    Or.inr (Or.inr (by
      ext w
      simp only [Set.mem_inter_iff, mem_cone, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro hw rfl
      exact h hw))
end

section

def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})
end

section

theorem singleton_cone_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ cone τ ∨ cone τ ⊆ ({σ} : Set Str) ∨ ({σ} : Set Str) ∩ cone τ = ∅ :=
  if h : τ <+: σ then
    Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h))
  else
    Or.inr (Or.inr (by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_cone, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl hw
      exact h hw))
end

section

theorem singleton_singleton_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ ({σ} : Set Str) ∨
      ({σ} : Set Str) ∩ ({τ} : Set Str) = ∅ := by
  by_cases h : σ = τ
  · subst h; exact Or.inl subset_rfl
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl h2
    exact h h2
end

section

theorem nestedOrDisjoint_C : NestedOrDisjoint memC := by
  rintro X Y hX hY
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩ <;> rcases hY with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · exact cone_trichotomy σ τ
  · exact cone_singleton_nd σ τ
  · exact singleton_cone_nd σ τ
  · exact singleton_singleton_nd σ τ
end

section

def C : NeighborhoodSystem Str :=
  ofNestedOrDisjoint memC Set.univ ⟨[], Set.mem_univ _⟩
    (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint_C
    (by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact Set.subset_univ _)
end

section
@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl
end

section
@[simp] theorem C_master : C.master = Set.univ := rfl
end

section

theorem memC_cone (σ : Str) : C.mem (cone σ) := Or.inl ⟨σ, rfl⟩
end

section

theorem memC_singleton (σ : Str) : C.mem ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩
end

section

theorem prepend_mono (σ : Str) {Y Y' : Set Str} (h : Y' ⊆ Y) : prepend σ Y' ⊆ prepend σ Y := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩
end

section

theorem prepend_singleton (σ ρ : Str) : prepend σ ({ρ} : Set Str) = ({σ ++ ρ} : Set Str) := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨τ, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨ρ, rfl, rfl⟩
end

section

theorem memC_prepend (σ : Str) {Y : Set Str} (hY : C.mem Y) : C.mem (prepend σ Y) := by
  rcases hY with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · rw [prepend_cone]; exact memC_cone (σ ++ ρ)
  · rw [prepend_singleton]; exact memC_singleton (σ ++ ρ)
end

section

theorem prepend_subset_cone (σ : Str) (Y : Set Str) : prepend σ Y ⊆ cone σ := by
  rintro w ⟨τ, _, rfl⟩
  exact mem_cone.mpr (List.prefix_append σ τ)
end

section

def singletonElt (σ : Str) : C.Element := C.principal (memC_singleton σ)
end

section

def Lambda : C.Element := singletonElt []
end

section

theorem subset_singleton_eq {W : Set Str} {σ : Str} (hW : C.mem W) (hsub : W ⊆ ({σ} : Set Str)) :
    W = ({σ} : Set Str) := by
  rcases hW with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact absurd hsub (cone_not_subset_singleton ρ σ)
  · rw [Set.singleton_subset_iff, Set.mem_singleton_iff] at hsub
    rw [hsub]
end

section

def juxtapose : ApproximableMap₂ C C C where
  rel X Y Z := C.mem Y ∧ C.mem Z ∧
    ((∃ σ, X = cone σ ∧ cone σ ⊆ Z) ∨ (∃ σ, X = ({σ} : Set Str) ∧ prepend σ Y ⊆ Z))
  rel_dom₀ := by
    rintro X Y Z ⟨_, _, (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)⟩
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_dom₁ := fun ⟨hY, _, _⟩ => hY
  rel_cod := fun ⟨_, hZ, _⟩ => hZ
  master_rel := ⟨C.master_mem, C.master_mem,
    Or.inl ⟨[], C_master.trans cone_nil.symm, by rw [C_master]; exact Set.subset_univ _⟩⟩
  inter_right := by
    rintro X Y Z Z' ⟨hY, hZ, hd⟩ ⟨_, hZ', hd'⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hd' with ⟨σ', hX', hsub'⟩ | ⟨σ', hX', _⟩
      · obtain rfl : σ = σ' := cone_injective hX'
        exact ⟨hY, C.inter_mem hZ hZ' (memC_cone σ) (Set.subset_inter hsub hsub'),
          Or.inl ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
      · exact absurd hX' (cone_ne_singleton σ σ')
    · rcases hd' with ⟨σ', hX', _⟩ | ⟨σ', hX', hsub'⟩
      · exact absurd hX'.symm (cone_ne_singleton σ' σ)
      · obtain rfl : σ = σ' := by
          have := hX'; rw [Set.singleton_eq_singleton_iff] at this; exact this
        exact ⟨hY, C.inter_mem hZ hZ' (memC_prepend σ hY) (Set.subset_inter hsub hsub'),
          Or.inr ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hY, _, hd⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hY', hZ', ?_⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hX' with ⟨σ', rfl⟩ | ⟨σ', rfl⟩
      · exact Or.inl ⟨σ', rfl, (hX'X.trans hsub).trans hZZ'⟩
      · refine Or.inr ⟨σ', rfl, ?_⟩
        have hσσ' : σ <+: σ' := mem_cone.mp (Set.singleton_subset_iff.mp hX'X)
        have h2 : cone σ' ⊆ cone σ := cone_subset_cone.mpr hσσ'
        exact ((prepend_subset_cone σ' Y').trans (h2.trans hsub)).trans hZZ'
    · obtain rfl : X' = ({σ} : Set Str) := subset_singleton_eq hX' hX'X
      exact Or.inr ⟨σ, rfl, ((prepend_mono σ hY'Y).trans hsub).trans hZZ'⟩
end

section

theorem bot_lt_Lambda : C.bot < Lambda := by
  refine lt_of_le_of_ne (C.bot_le _) ?_
  intro h
  have hmem : C.bot.mem ({([] : Str)} : Set Str) := by
    rw [h]; exact ⟨memC_singleton [], subset_rfl⟩
  rw [C.mem_bot, C_master] at hmem
  have h2 : ([true] : Str) ∈ ({([] : Str)} : Set Str) := by rw [hmem]; trivial
  rw [Set.mem_singleton_iff] at h2
  exact absurd h2 (by decide)
end

section

theorem isTotal_singletonElt (σ : Str) : C.IsTotal (singletonElt σ) := by
  intro y hy Z hZ
  have hσy : y.mem ({σ} : Set Str) := hy {σ} ⟨memC_singleton σ, subset_rfl⟩
  have hinter : y.mem (({σ} : Set Str) ∩ Z) := y.inter_mem hσy hZ
  have hmemC : C.mem (({σ} : Set Str) ∩ Z) := y.sub hinter
  have heq : ({σ} : Set Str) ∩ Z = ({σ} : Set Str) :=
    subset_singleton_eq hmemC Set.inter_subset_left
  exact ⟨y.sub hZ, by rw [← heq]; exact Set.inter_subset_right⟩
end

section

theorem juxtapose_cone (σ : Str) (y : C.Element) :
    juxtapose.toElementMap₂ (C.principal (memC_cone σ)) y = C.principal (memC_cone σ) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, ⟨_, hconeX⟩, _, hY, hZ, hd⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, _⟩
    · exact ⟨hZ, hconeX.trans hsub⟩
    · exact absurd hconeX (cone_not_subset_singleton σ ρ)
  · rintro ⟨hZ, hconeσZ⟩
    exact ⟨cone σ, C.master, ⟨memC_cone σ, subset_rfl⟩, y.master_mem, C.master_mem, hZ,
      Or.inl ⟨σ, rfl, hconeσZ⟩⟩
end

section

theorem juxtapose_singleton_mem (σ : Str) (y : C.Element) {Z : Set Str} :
    (juxtapose.toElementMap₂ (singletonElt σ) y).mem Z ↔
      C.mem Z ∧ ∃ Y', y.mem Y' ∧ prepend σ Y' ⊆ Z := by
  constructor
  · rintro ⟨X, Y, ⟨_, hsingleX⟩, hYmem, _, hZ, hd⟩
    refine ⟨hZ, ?_⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, hsub⟩
    · have hρσ : ρ <+: σ := mem_cone.mp (Set.singleton_subset_iff.mp hsingleX)
      refine ⟨C.master, y.master_mem, ?_⟩
      rw [C_master, prepend_univ]
      exact (cone_subset_cone.mpr hρσ).trans hsub
    · obtain rfl : σ = ρ := by
        have := Set.singleton_subset_iff.mp hsingleX
        rwa [Set.mem_singleton_iff] at this
      exact ⟨Y, hYmem, hsub⟩
  · rintro ⟨hZ, Y', hY'mem, hsub⟩
    exact ⟨{σ}, Y', ⟨memC_singleton σ, subset_rfl⟩, hY'mem, y.sub hY'mem, hZ,
      Or.inr ⟨σ, rfl, hsub⟩⟩
end

section
set_option linter.unusedVariables false

theorem example_221 : ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
  (y :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Exercise221.C)
  {Z : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str},
  Iff
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Exercise221.C
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.toElementMap₂ DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Exercise221.C DomainTheory.NeighbourhoodSystems.Exercise221.C
        DomainTheory.NeighbourhoodSystems.Exercise221.C DomainTheory.NeighbourhoodSystems.Exercise221.juxtapose
        (DomainTheory.NeighbourhoodSystems.Exercise221.singletonElt σ) y)
      Z)
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Exercise221.C Z)
      (∃ (Y' : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise221.C y Y')
          (@LE.le (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instLE DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.ExampleB.prepend σ Y') Z))) :=
  DomainTheory.NeighbourhoodSystems.Exercise221.juxtapose_singleton_mem
end

section

theorem memB_imp_memC {X : Set Str} (hX : B.mem X) : C.mem X := by
  obtain ⟨σ, rfl⟩ := hX; exact memC_cone σ
end

section

theorem memC_nonempty {W : Set Str} (hW : C.mem W) : W.Nonempty := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨σ, mem_cone.mpr List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise221
