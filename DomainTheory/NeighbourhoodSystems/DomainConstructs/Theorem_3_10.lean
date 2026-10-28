module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Definition_3_8

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

def toApproxMap (φ : (funSpace V₀ V₁).Element) : ApproximableMap V₀ V₁ where
  rel X Y := φ.mem (step X Y)
  rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_dom hf
  rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_cod hf
  master_rel := by show φ.mem (step V₀.master V₁.master); rw [step_master_eq]; exact φ.master_mem
  inter_right := by
    intro X Y Y' h h'
    obtain ⟨f, hf⟩ := (φ.sub h).2
    obtain ⟨f', hf'⟩ := (φ.sub h').2
    have hY : V₁.mem Y := f.rel_cod hf
    have hY' : V₁.mem Y' := f'.rel_cod hf'
    show φ.mem (step X (Y ∩ Y'))
    rw [← step_inter_right hY hY']
    exact φ.inter_mem h h'
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY'
    show φ.mem (step X' Y')
    exact φ.up_mem h (step_mem hX' hY') (step_subset hX' hY' hX'X hYY')

@[simp] theorem toApproxMap_rel {φ : (funSpace V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toApproxMap φ).rel X Y ↔ φ.mem (step X Y) := Iff.rfl

def toFilter (f : ApproximableMap V₀ V₁) : (funSpace V₀ V₁).Element where
  mem W := (funSpace V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(funSpace V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
    refine ⟨⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, ⟨f, ?_⟩⟩, ?_⟩
    · intro p hp; rcases List.mem_append.mp hp with h | h
      · exact hL p h
      · exact hL' p h
    · exact Set.mem_inter hfW hfW'
    · exact Set.mem_inter hfW hfW'
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

@[simp] theorem mem_toFilter {f : ApproximableMap V₀ V₁} {W : Set (ApproximableMap V₀ V₁)} :
    (toFilter f).mem W ↔ (funSpace V₀ V₁).mem W ∧ f ∈ W := Iff.rfl

def funSpaceEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ V₁).Element ≃o ApproximableMap V₀ V₁ where
  toFun := toApproxMap
  invFun := toFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_stepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_stepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨step_mem (f.rel_dom hf) (f.rel_cod hf), hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_stepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_stepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

@[simp] theorem funSpaceEquiv_apply (φ : (funSpace V₀ V₁).Element) :
    funSpaceEquiv V₀ V₁ φ = toApproxMap φ := rfl

@[simp] theorem funSpaceEquiv_symm_apply (f : ApproximableMap V₀ V₁) :
    (funSpaceEquiv V₀ V₁).symm f = toFilter f := rfl

theorem funSpace_mem_inter {W W' : Set (ApproximableMap V₀ V₁)}
    (hW : (funSpace V₀ V₁).mem W) (hW' : (funSpace V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (funSpace V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

end
end DomainTheory.NeighbourhoodSystems
end
