/-ai
The first projection of the product is a computable map.

Inclusion in the first presentation is recursively decidable. Reindex it so that the domain index is the first factor of the product code. That predicate matches the projection relation, because the left preimage of a product neighbourhood is the first factor: one direction reads the inclusion, and the other restores product membership together with the codomain neighbourhood.
ai-/
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





/-- **Theorem 7.4 (Scott 1981, PRG-19) — `proj₀` is computable.** `(Xₙ⁰ ∪ Xₘ¹) p₀ X⁰_k ↔ Xₙ⁰ ⊆ X⁰_k`,
a recursive slice of `incl_computable`, hence r.e. -/
theorem proj₀_isComputable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    IsComputableMap (prodPresentation P₀ P₁) P₀ (proj₀ V₀ V₁) := by
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [prodPresentation_X, proj₀_rel, inl_preimage_prodNbhd, unpair_pair_fst, unpair_pair_snd]
  exact ⟨fun h => h.2.2,
    fun h => ⟨prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _), P₀.mem_X _, h⟩⟩

end DomainTheory.NeighbourhoodSystems
