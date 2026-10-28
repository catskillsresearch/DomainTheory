module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def boxTag (i : ℕ) (x : Pomega) : Pomega :=
  condSet x (ofNat i) (ofNat i)

namespace boxTag

theorem bot (i : ℕ) : boxTag i botElem = botElem := by
  ext n
  simp [boxTag, condSet, botElem]

theorem isScottContinuous (i : ℕ) : IsScottContinuous (boxTag i) := by
  have hfun : boxTag i = fun z => condSet z (ofNat i) (ofNat i) := rfl
  rw [hfun]
  exact condSet.isScottContinuous_left (ofNat i) (ofNat i)

theorem of_mem {x : Pomega} {m : ℕ} (hm : m ∈ x) (i : ℕ) :
    boxTag i x = ofNat i := by
  ext n
  simp only [boxTag, condSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  · intro hn
    cases m with
    | zero => exact Or.inl ⟨hn, hm⟩
    | succ k => exact Or.inr ⟨hn, k, hm⟩

end boxTag

end DomainTheory.DataTypesAsLattices
