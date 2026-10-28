
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Enumeration.applyNat
public import DomainTheory.DataTypesAsLattices.Enumeration.RE
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_1
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Graph.Basic.notation3
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem theorem_3_2 :
    (∀ n, valNat n ∈ RE) ∧
      valNat 0 = Gcomb ∧
        (∀ n m, valNat (applyNat n m) = valNat n ⬝ valNat m) :=
  ⟨fun n => valNat.combinatory n, valNat.zero, valNat.app⟩

namespace theorem_3_2

theorem surjective {u : Pomega} (hu : IsCombinatory u) :
    ∃ n, valNat n = u := by
  revert hu
  rw [theorem_3_1]
  intro h
  induction h with
  | G => exact ⟨0, valNat.zero⟩
  | app _ _ iu iv =>
    obtain ⟨n, hn⟩ := iu
    obtain ⟨m, hm⟩ := iv
    exact ⟨applyNat n m, by rw [valNat.app, hn, hm]⟩

theorem i : condSet (ofNat 0) Gcomb botElem = Gcomb := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨hG, _⟩ | ⟨_, ⟨k, hk⟩⟩
    · exact hG
    · simp [ofNat] at hk
  · intro hG
    exact Or.inl ⟨hG, rfl⟩

theorem range : RE = Set.range valNat := by
  ext u
  constructor
  · intro hu
    exact theorem_3_2.surjective hu
  · intro ⟨n, hn⟩
    simpa [← hn] using (theorem_3_2).1 n

end theorem_3_2

end DomainTheory.DataTypesAsLattices
