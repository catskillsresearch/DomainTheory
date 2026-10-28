module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedLattices.DirectedSet
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Embedding.extend
public import DomainTheory.DataTypesAsLattices.Embedding.embed
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.DirectedSubset
public import DomainTheory.DataTypesAsLattices.Retracts.typed
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis
public import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_1

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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

theorem theorem_4_1.continuous {a : Pomega} (ha : Retract a) :
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
    directed_finite_cover hs' (e_finite n) (by simpa [Fixpoints.vals] using hen)
  refine ⟨z, hz, ?_⟩
  rw [hyn]
  have := IsScottContinuous.monotone (funOf.isScottContinuous a) hnz
  rwa [z.property] at this

end DomainTheory.DataTypesAsLattices
