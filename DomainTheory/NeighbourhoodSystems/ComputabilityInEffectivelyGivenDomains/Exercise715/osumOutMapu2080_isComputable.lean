/-ai
The coalesced left projection is a computable map from the coalesced-sum presentation to the Scott presentation of the left system.

The relation holds exactly when the left part of the enumerated neighbourhood is contained in the target. On a proper left code the left part is the indexed left neighbourhood. On a proper right code or the master, the left part is the left master, and inclusion of the master is inclusion against an index of the master, which exists by surjectivity. The tag test, properness, and these inclusions are recursively decidable, so the relation is recursively decidable and hence recursively enumerable.
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


/-- **`out₀` is computable.** `(osumEnum n) (out₀) X⁰_m ↔ leftPart (osumEnum n) ⊆ X⁰_m`; the left
part is `X⁰_{n.2}` on a proper left copy and `Δ₀` on a right copy / the master, so the relation is
`incl` against either `n.2` or the master index `k₀` (`X⁰_{k₀} = Δ₀`). -/
theorem osumOutMap₀_isComputable :
    IsComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) P₀.toScott osumOutMap₀ := by
  obtain ⟨k0, hk0⟩ := P₀.surj V₀.master_mem
  have hT0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have hIncL : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ⊆ P₀.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₀.incl_computable.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hIncM : RecDecidable (fun t => V₀.master ⊆ P₀.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd, hk0])
      (P₀.incl_computable.comp ((Nat.Primrec.const k0).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT0.and (hP0.and hIncL)).or ((hT0.and hP0).not.and hIncM))).re
  show (osumOutMap₀ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2) ↔ _
  rw [show (osumOutMap₀ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2)
      ↔ leftPart V₀ (osumEnum P₀ P₁ t.unpair.1) ⊆ P₀.X t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨osumEnum_mem h₀ h₁ _, P₀.mem_X _, h⟩⟩]
  by_cases hL : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL, leftPart_inj₀]
    exact ⟨fun h => Or.inl ⟨hL.1, hL.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hL h.1)⟩
  · by_cases hR : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _))]
      exact ⟨fun h => Or.inr ⟨hL, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL) (fun h => h.2)⟩
    · rw [osumEnum_master hL hR, leftPart_sumMaster]
      exact ⟨fun h => Or.inr ⟨hL, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL) (fun h => h.2)⟩

end Coalesced
end DomainTheory.NeighbourhoodSystems
