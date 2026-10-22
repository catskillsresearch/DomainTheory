module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 7.4 (Scott 1981, PRG-19) — `proj₁` is computable.** `(Xₙ⁰ ∪ Xₘ¹) p₁ X¹_k ↔ Xₘ¹ ⊆ X¹_k`
(Scott's worked example), a recursive slice of `incl_computable`. -/
theorem proj₁_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputableMap (prodPresentation P₀ P₁) P₁ (proj₁ V₀ V₁) := by
  constructor
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₁_rel, inr_preimage_prodNbhd, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₁.mem_X _, h⟩⟩

end DomainTheory.NeighbourhoodSystems
