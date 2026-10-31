module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

theorem proposition_3_10 (hD : ContinuousLattice D) (hD' : ContinuousLattice D') (i : D → D') :
    ((∀ S : Set D, i (sSup S) = sSup (Set.image i S))
      ∧ Function.Injective i
      ∧ (∀ x y : D, x ≪ y → i x ≪ i y))
      ↔
    (∃ P : ContinuousLatticeProjection D D',
      (∀ d, (P.incl : D → D') d = i d)
        ∧ (∀ x', (P.retr : D' → D) x' = sSup { x | i x ≤ x' })) := by
  constructor
  · rintro ⟨hi, hinj, hwb⟩
    refine ⟨ContinuousLatticeProjection.converseProjection i hi hinj
      (fun {x y} h => hwb x y h) hD, fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨P, hincl, _⟩
    refine ⟨?_, ?_, ?_⟩
    · intro S
      rw [← hincl (sSup S), P.incl_sSup]
      congr 1
      ext y
      simp [Set.mem_image, hincl]
    · intro x y h
      have h' : (P.incl : D → D') x = (P.incl : D → D') y := by rw [hincl x, hincl y, h]
      exact P.incl_injective h'
    · intro x y h
      rw [← hincl x, ← hincl y]
      exact P.incl_wayBelow hD' h

end DomainTheory.ContinuousLattice
