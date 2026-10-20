module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.not_sum_reaches_both
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_sumComb_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **On a "left" point** (`jPlus x` reaches the left copy), `sumComb a b` evaluates to Scott's
literal `i₊∘in₀∘a∘out₀` formula. -/
theorem toElementMap_sumComb_of_left {a b : ApproximableMap U U} {x : U.Element}
    (hL : ∃ X, U.mem X ∧ (jPlus.toElementMap x).mem (inj₀ X)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have hz : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := which_mem_zero.mpr hL
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one :=
    fun h => not_sum_reaches_both hL (which_mem_one.mp h)
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | rfl)
    · exact h
    · exact absurd h1 hno
    · exact Element.master_mem _
  · intro h
    exact Or.inl ⟨hz, h⟩

end DomainTheory.NeighbourhoodSystems
