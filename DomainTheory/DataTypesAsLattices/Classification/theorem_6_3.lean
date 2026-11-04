module

public import DomainTheory.DataTypesAsLattices.Classification.Classes
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
import DomainTheory.DataTypesAsLattices.Classification.CharacteristicMaps
import DomainTheory.DataTypesAsLattices.Classification.pairIndexed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

theorem theorem_6_3 :
    ∀ U, IsScottGdelta U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x = topElem} := by
  intro U
  constructor
  · rintro ⟨Us, hUs, rfl⟩
    let fs := fun n => charTop (Us n)
    refine ⟨pairIndexed fs, pairIndexed.isScottContinuous fs fun n =>
      charTop.isScottContinuous (Us n), ?_⟩
    ext x
    constructor
    · intro hx
      change pairIndexed fs x = topElem
      exact (pairIndexed.eq_top fs x).mpr fun n =>
        (charTop.eq_top (hUs n) x).mpr (Set.mem_iInter.mp hx n)
    · intro hf
      have hf' : pairIndexed fs x = topElem := hf
      exact Set.mem_iInter.mpr fun n =>
        (charTop.eq_top (hUs n) x).mp ((pairIndexed.eq_top fs x).mp hf' n)
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun n => {x | n ∈ f x}, fun n => IsScottContinuous.mem_preimage hf n, ?_⟩
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun n => ?_
      have : f x = topElem := hx
      simp [this]
    · intro hx
      ext k
      constructor
      · intro _; trivial
      · intro _
        exact Set.mem_iInter.mp hx k

end DomainTheory.DataTypesAsLattices
