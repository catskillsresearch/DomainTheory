module

public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace theorem_4_1

theorem complete (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints f :=
  gfpBelow.mem f hf A hA

theorem continuous {a : Pomega} (ha : Retract a) :
    ∀ x : Fixpoints (funOf a),
      DirectedSubset (retractBasis a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) ∧
        ∀ y ∈ retractBasis a x,
          ∀ s : Set (Fixpoints (funOf a)),
            DirectedSubset s →
              (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
              ∃ z ∈ s, (y : Pomega) ⊆ z := by
  intro x
  refine ⟨retractBasis.directedSubset ha x, retractBasis.eq_sUnion ha x, ?_⟩
  intro y hy s hs hxs
  obtain ⟨n, hnx, hyn⟩ := hy
  have hen : e n ⊆ ⋃₀ (Subtype.val '' s) := hnx.trans hxs
  have hs' : DirectedSet s :=
    ⟨⟨hs.out.1, fun u hu v hv => by
      obtain ⟨w, hw, huw, hvw⟩ := hs.out.2 hu hv
      exact ⟨w, hw, huw, hvw⟩⟩⟩
  obtain ⟨z, hz, hnz⟩ :=
    directed_finite_cover hs' (e.finite n) (by simpa [Fixpoints.vals] using hen)
  refine ⟨z, hz, ?_⟩
  rw [hyn]
  have := IsScottContinuous.monotone (funOf.isScottContinuous a) hnz
  rwa [z.property] at this

end theorem_4_1

theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (_ha : Retract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          ∀ x : Fixpoints (funOf a),
            DirectedSubset (retractBasis a x) ∧
              (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  constructor
  · intro A hA
    exact ⟨theorem_4_1.complete f hf A hA, lfpAbove.mem hf hA⟩
  · intro a ha
    constructor
    · ext x
      simp [Fixpoints, typed, eq_comm]
    · intro x
      exact ⟨retractBasis.directedSubset ha x, retractBasis.eq_sUnion ha x⟩

end DomainTheory.DataTypesAsLattices
