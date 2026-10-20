module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-- **Exercise 7.21 — the two-variable combinator `papplyEval : ℙ(D→E) × ℙD → ℙE`.** The Smyth
power-domain lift of evaluation (Theorem 3.11): a `ℙ(D→E)`-neighbourhood `Φ` applied to a
`ℙD`-neighbourhood `A` covers a `ℙE`-neighbourhood `B` iff every function-neighbourhood `G ∈ Φ`
applied to every argument-neighbourhood `X ∈ A` lands in some `Y ∈ B` (via `eval`, i.e. every
`f ∈ G` sends `X` into `Y`). This is the two-variable analogue of Exercise 7.19's `ℙf`. -/
def papplyEval (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap₂ (funSpace V W).PowerDomain V.PowerDomain W.PowerDomain where
  rel Φ A B := (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
    ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := by
    refine ⟨(funSpace V W).PDmem_master, V.PDmem_master, W.PDmem_master, ?_⟩
    intro G hG X hX
    simp only [mem_upSet] at hG hX
    refine ⟨W.master, ⟨W.master_mem, subset_rfl⟩, ?_⟩
    exact ⟨hG.1, hX.1, W.master_mem,
      fun f hf => f.mono f.master_rel (V.sub_master hX.1) subset_rfl hX.1 W.master_mem⟩
  inter_right := by
    rintro Φ A B B' ⟨hΦ, hA, hB, hbody⟩ ⟨-, -, hB', hbody'⟩
    refine ⟨hΦ, hA, W.PDmem_inter hB hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G hG X hX
    obtain ⟨Y', hY'B', hrel'⟩ := hbody' G hG X hX
    have hinmem : W.mem (Y ∩ Y') := (eval V W).rel_cod ((eval V W).inter_right hrel hrel')
    exact ⟨Y ∩ Y', Set.mem_inter
      (W.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (W.PDmem_down hB' hY'B' Set.inter_subset_right hinmem),
      (eval V W).inter_right hrel hrel'⟩
  mono := by
    rintro Φ Φ' A A' B B' ⟨_, _, _, hbody⟩ hΦ'Φ hA'A hBB' hΦ' hA' hB'
    refine ⟨hΦ', hA', hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G (hΦ'Φ hG) X (hA'A hX)
    exact ⟨Y, hBB' hYB, hrel⟩

end DomainTheory.NeighbourhoodSystems
