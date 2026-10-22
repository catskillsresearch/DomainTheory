/-ai
The coalesced left injection is a computable map from the Scott presentation of the left system into the coalesced-sum presentation.

The relation holds exactly when the left injection of the domain neighbourhood is contained in the enumerated codomain. Equality of tags, properness, and inclusion are recursively decidable. On a proper left code the inclusion is inclusion of left neighbourhoods. On a proper right code it fails, because a point of the nonempty domain neighbourhood lies in the left injection and not in the right injection. On the master it holds, because every left injection is contained in the separated-sum master. That decidable combination is recursively enumerable.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


open Exercise510


section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


variable {h₀ h₁}


variable (P₀ P₁)


/-- **`in₀` is computable.** `X⁰ₙ (in₀) (osumEnum m)` decodes to: `m` a proper left copy with
`X⁰ₙ ⊆ X⁰_{m.2}`, or `m` the master (`inj₀` of a proper neighbourhood always sits under the master);
the proper-right case is impossible (`inj₀` of a nonempty set is not `⊆ inj₁`). -/
theorem osumInMap₀_isComputable :
    ComputableMapS P₀.toScott (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) osumInMap₀ := by
  constructor
  have hT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hInc : RecDecidable (fun t => P₀.X t.unpair.1 ⊆ P₀.X t.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₀.incl_computable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT0.and (hP0.and hInc)).or ((hT0.and hP0).not.and (hT1.and hP1).not))).re
  show (osumInMap₀ (h₀ := h₀) (h₁ := h₁)).rel (P₀.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2) ↔ _
  rw [show (osumInMap₀ (h₀ := h₀) (h₁ := h₁)).rel (P₀.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2)
      ↔ inj₀ (P₀.X t.unpair.1) ⊆ osumEnum P₀ P₁ t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨P₀.mem_X _, osumEnum_mem h₀ h₁ _, h⟩⟩]
  by_cases hL : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL, inj₀_subset_inj₀]
    exact ⟨fun h => Or.inl ⟨hL.1, hL.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hL h.1)⟩
  · by_cases hR : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]
      refine ⟨fun h => ?_, fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL)
        (fun h => absurd hR h.2)⟩
      obtain ⟨a, ha⟩ := h₀ _ (P₀.mem_X t.unpair.1)
      exact absurd (h (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rw [osumEnum_master hL hR]
      exact ⟨fun _ => Or.inr ⟨hL, hR⟩, fun _ => inj₀_subset_sumMaster (P₀.mem_X _)⟩

end Coalesced
end DomainTheory.NeighbourhoodSystems
