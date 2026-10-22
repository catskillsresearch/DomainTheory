module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}


/-- **Choice-free witness gathering (single list).** From `∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y`, build one
list `M` of `(X, Y)` pairs, each drawn from `L₁ × L₂` and `f`-related, that *covers* `L₁`: every
`X ∈ L₁` has a matching `Y` with `(X, Y) ∈ M`. (The one-map analogue of `comp_witness`.) -/
theorem gather_witnesses (f : ApproximableMap V W) :
    ∀ (L₁ : List (Set α)) (L₂ : List (Set β)), (∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y) →
      ∃ M : List (Set α × Set β), (∀ p ∈ M, p.1 ∈ L₁ ∧ p.2 ∈ L₂ ∧ f.rel p.1 p.2) ∧
        ∀ X ∈ L₁, ∃ Y ∈ L₂, (X, Y) ∈ M := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ _; exact ⟨[], by simp, by simp⟩
  | cons X L₁ ih =>
    intro L₂ h
    obtain ⟨Y, hY, hrel⟩ := h X (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨M, hMprop, hMwit⟩ := ih L₂ (fun X' hX' => h X' (List.mem_cons.mpr (Or.inr hX')))
    refine ⟨(X, Y) :: M, ?_, ?_⟩
    · rintro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨List.mem_cons.mpr (Or.inl rfl), hY, hrel⟩
      · obtain ⟨hX1, hY1, hrel1⟩ := hMprop p hp'
        exact ⟨List.mem_cons.mpr (Or.inr hX1), hY1, hrel1⟩
    · intro X' hX'
      rcases List.mem_cons.mp hX' with rfl | hX''
      · exact ⟨Y, hY, List.mem_cons.mpr (Or.inl rfl)⟩
      · obtain ⟨Y', hY', hmem⟩ := hMwit X' hX''
        exact ⟨Y', hY', List.mem_cons.mpr (Or.inr hmem)⟩

end DomainTheory.NeighbourhoodSystems
