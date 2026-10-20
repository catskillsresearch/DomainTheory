module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.PFmap_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}

/-- **Exercise 7.19 — the combinator `λf. ℙf : (D → E) → (ℙD → ℙE)`.** The flat Smyth-style lift
`(Φ, Ψ) ↦ mem Φ ∧ mem Ψ ∧ ∀ f ∈ Φ, ℙf ∈ Ψ` of Exercise 7.19's functorial action, one level up on the
function spaces (`funSpace`, Theorem 3.10) — the same recipe as Exercise 7.16's `curryComb` and
Exercise 7.21's `papplyEval`. Approximability is immediate: unlike `PFmap` itself, the body is a bare
membership check with no witnesses to gather. -/
def PFmapComb (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W) (funSpace V.PowerDomain W.PowerDomain) where
  rel Φ Ψ := (funSpace V W).mem Φ ∧ (funSpace V.PowerDomain W.PowerDomain).mem Ψ ∧
    ∀ f ∈ Φ, PFmap f ∈ Ψ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel :=
    ⟨(funSpace V W).master_mem, (funSpace V.PowerDomain W.PowerDomain).master_mem,
      fun _ _ => Set.mem_univ _⟩
  inter_right := by
    rintro Φ Ψ Ψ' ⟨hΦ, hΨ, hbody⟩ ⟨-, hΨ', hbody'⟩
    obtain ⟨f₀, hf₀⟩ := hΦ.2
    obtain ⟨⟨L₂, hL₂, rfl⟩, -⟩ := hΨ
    obtain ⟨⟨L₂', hL₂', rfl⟩, -⟩ := hΨ'
    refine ⟨hΦ, ⟨⟨L₂ ++ L₂', ?_, (stepFun_append _ _).symm⟩,
        ⟨PFmap f₀, Set.mem_inter (hbody f₀ hf₀) (hbody' f₀ hf₀)⟩⟩,
      fun f hf => Set.mem_inter (hbody f hf) (hbody' f hf)⟩
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · exact hL₂ q hq'
    · exact hL₂' q hq'
  mono := by
    rintro Φ Φ' Ψ Ψ' ⟨_, _, hbody⟩ hΦ'Φ hΨΨ' hΦ' hΨ'
    exact ⟨hΦ', hΨ', fun f hf => hΨΨ' (hbody f (hΦ'Φ hf))⟩

end DomainTheory.NeighbourhoodSystems
