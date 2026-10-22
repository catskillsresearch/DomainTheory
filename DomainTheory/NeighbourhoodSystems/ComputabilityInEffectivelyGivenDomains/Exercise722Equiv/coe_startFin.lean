module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set


theorem coe_startFin : ∀ e : SExpr, (↑(startFin e) : Set (autState e)) = (toNFA e).start
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.start
      show (↑(Finset.univ : Finset Unit) : Set Unit) = {sigmaDFA.start}
      ext x; cases x; simp
  | .single σ => by
      show (↑({(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)} : Finset (SingleState σ)) : Set _)
        = (singleDFA σ).toNFA.start
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      show (↑((startFin a) ×ˢ (startFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).start
      rw [Finset.coe_product, coe_startFin a, coe_startFin b]
      rfl
  | .cat a b => by
      show (↑(if ((startFin a) ∩ (acceptFin a)).Nonempty
          then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (startFin a).image (inl : autState a → autState a ⊕ autState b)) :
          Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.start
      show _ = (catEps (toNFA a) (toNFA b)).εClosure (catEps (toNFA a) (toNFA b)).start
      rw [catEps_start]
      by_cases hne : ((startFin a) ∩ (acceptFin a)).Nonempty
      · rw [ite_eq_left hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_startFin a, ← coe_acceptFin a, ← coe_startFin b]
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
        rw [catEps_mem_εClosure_iff, ← coe_startFin a, ← coe_acceptFin a, ← coe_startFin b]
        simp only [Finset.coe_image, mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, hq1, q', hq2, heq⟩, _⟩)
          · exact ⟨q, hq, rfl⟩
          · cases heq
            exact absurd ⟨q, Finset.mem_inter.mpr ⟨hq2, hq1⟩⟩ hne

end Exercise722
end DomainTheory.NeighbourhoodSystems
