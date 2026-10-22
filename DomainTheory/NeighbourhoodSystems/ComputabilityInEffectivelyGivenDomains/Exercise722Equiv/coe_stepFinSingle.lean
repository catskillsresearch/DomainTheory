module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.coe_startFin

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


theorem coe_stepFinSingle : ∀ (e : SExpr) (s : autState e) (c : Bool),
    (↑(stepFinSingle e s c) : Set (autState e)) = (toNFA e).step s c
  | .sigma, s, c => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.step s c
      show (↑(Finset.univ : Finset Unit) : Set Unit) = {sigmaDFA.step s c}
      ext x; cases x; simp
  | .single σ, s, c => by
      show (↑({(singleDFA σ).step s c} : Finset (SingleState σ)) : Set _)
        = (singleDFA σ).toNFA.step s c
      simp [DFA.toNFA]
  | .cap a b, (s1, s2), c => by
      show (↑((stepFinSingle a s1 c) ×ˢ (stepFinSingle b s2 c)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).step (s1, s2) c
      rw [Finset.coe_product, coe_stepFinSingle a s1 c, coe_stepFinSingle b s2 c]
      rfl
  | .cat a b, inl s, c => by
      show (↑(if ((stepFinSingle a s c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s c).image (inl : autState a → autState a ⊕ autState b)) :
          Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.step (inl s) c
      show _ = (catEps (toNFA a) (toNFA b)).εClosure
        ((catEps (toNFA a) (toNFA b)).step (inl s) (some c))
      rw [catEps_step_inl_some]
      by_cases hne : ((stepFinSingle a s c) ∩ (acceptFin a)).Nonempty
      · rw [ite_eq_left hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle a s c, ← coe_acceptFin a,
          ← coe_startFin b]
        simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
        constructor
        · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · refine Or.inr ⟨?_, q, hq, rfl⟩
            obtain ⟨q0, hq0⟩ := hne
            rw [Finset.mem_inter] at hq0
            exact ⟨q0, hq0.2, q0, hq0.1, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨_, q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · exact Or.inr ⟨q, hq, rfl⟩
      · rw [ite_eq_right hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle a s c, ← coe_acceptFin a,
          ← coe_startFin b]
        simp only [Finset.coe_image, mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, hq1, q', hq2, heq⟩, _⟩)
          · exact ⟨q, hq, rfl⟩
          · cases heq
            exact absurd ⟨q, Finset.mem_inter.mpr ⟨hq2, hq1⟩⟩ hne
  | .cat a b, inr s, c => by
      show (↑((stepFinSingle b s c).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.step (inr s) c
      show _ = (catEps (toNFA a) (toNFA b)).εClosure
        ((catEps (toNFA a) (toNFA b)).step (inr s) (some c))
      rw [catEps_step_inr_some]
      ext x
      rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle b s c]
      simp only [Finset.coe_image, mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
      · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, _, hqmem⟩, _⟩)
        · exact ⟨q, hq, rfl⟩
        · exact absurd hqmem (by simp)

end Exercise722
end DomainTheory.NeighbourhoodSystems
