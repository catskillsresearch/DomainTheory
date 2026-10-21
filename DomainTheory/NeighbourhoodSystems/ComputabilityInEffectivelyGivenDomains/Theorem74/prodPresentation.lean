/-ai
The product presentation enumerates, at each code, the product neighbourhood of the two component neighbourhoods read off by unpairing. Every such set is a product neighbourhood, and every product neighbourhood arises by pairing indices of its factors. Equality of an intersection of two enumerated neighbourhoods with a third, and consistency of a pair, are the conjunctions of the two factors' corresponding decidable relations after primitive-recursive reindexing; the consistency equivalence packs and unpacks a paired index. The intersection code pairs the factors' intersection codes and is primitive recursive because each factor's intersection is. On a consistent pair it equals the intersection, by splitting the product inclusion and applying each factor's intersection specification. The master code is the pair of the two master codes, and it enumerates the product of the two masters.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodNbhd_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74.prodEnum_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 7.4 (Scott 1981, PRG-19) — `𝒟₀ × 𝒟₁` is effectively given.** The presentation
`W_k = X⁰_{p k} ∪ X¹_{q k}`. Scott's 7.1(i) and (ii) each split, via `prodNbhd_inter` /
`prodNbhd_subset_iff`, into the *conjunction* of the two factors' relations on the projected
indices — recursively decidable by `RecDecidable.and`/`.comp`/`.of_iff`. -/
def prodPresentation (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) :
    ComputablePresentation (prod V₀ V₁) where
  X := prodEnum P₀ P₁
  mem_X t := prod_mem_prodNbhd (P₀.mem_X _) (P₁.mem_X _)
  surj := by
    rintro Z ⟨X, Y, hX, hY, rfl⟩
    obtain ⟨n, rfl⟩ := P₀.surj hX
    obtain ⟨m, rfl⟩ := P₁.surj hY
    exact ⟨Nat.pair n m, by simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd]⟩
  interEq_computable := by
    have hIE0 : RecDecidable (fun s => P₀.X s.unpair.1 ∩ P₀.X s.unpair.2.unpair.1
        = P₀.X s.unpair.2.unpair.2) := P₀.interEq_computable
    have hIE1 : RecDecidable (fun s => P₁.X s.unpair.1 ∩ P₁.X s.unpair.2.unpair.1
        = P₁.X s.unpair.2.unpair.2) := P₁.interEq_computable
    have hg0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1
        (Nat.pair t.unpair.2.unpair.1.unpair.1 t.unpair.2.unpair.2.unpair.1)) :=
      (Nat.Primrec.left.comp Nat.Primrec.left).pair
        ((Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    have hg1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2
        (Nat.pair t.unpair.2.unpair.1.unpair.2 t.unpair.2.unpair.2.unpair.2)) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair
        ((Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_) ((hIE0.comp hg0).and (hIE1.comp hg1))
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, prodNbhd_inter, prodNbhd_eq_iff]
  cons_computable := by
    have hC0 : RecDecidable (fun s => ∃ k, P₀.X k ⊆ P₀.X s.unpair.1 ∩ P₀.X s.unpair.2) :=
      P₀.cons_computable
    have hC1 : RecDecidable (fun s => ∃ k, P₁.X k ⊆ P₁.X s.unpair.1 ∩ P₁.X s.unpair.2) :=
      P₁.cons_computable
    have hh0 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
      (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.left.comp Nat.Primrec.right)
    have hh1 : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
    refine RecDecidable.of_iff (fun t => ?_) ((hC0.comp hh0).and (hC1.comp hh1))
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, prodNbhd_inter,
      prodNbhd_subset_iff]
    constructor
    · rintro ⟨k, hk0, hk1⟩
      exact ⟨⟨k.unpair.1, hk0⟩, ⟨k.unpair.2, hk1⟩⟩
    · rintro ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩⟩
      exact ⟨Nat.pair k0 k1, by simpa only [unpair_pair_fst] using hk0,
        by simpa only [unpair_pair_snd] using hk1⟩
  inter n m := Nat.pair (P₀.inter n.unpair.1 m.unpair.1) (P₁.inter n.unpair.2 m.unpair.2)
  inter_primrec := by
    have h0 : Nat.Primrec (fun t => P₀.inter t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
      (P₀.inter_primrec.comp ((Nat.Primrec.left.comp Nat.Primrec.left).pair
        (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq fun t => by
          simp only [unpair_pair_fst, unpair_pair_snd]
    have h1 : Nat.Primrec (fun t => P₁.inter t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
      (P₁.inter_primrec.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right))).of_eq fun t => by
          simp only [unpair_pair_fst, unpair_pair_snd]
    exact h0.pair h1
  inter_spec := by
    rintro n m ⟨k, hk⟩
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd] at hk ⊢
    rw [prodNbhd_inter] at hk ⊢
    obtain ⟨h0, h1⟩ := prodNbhd_subset_iff.mp hk
    rw [P₀.inter_spec ⟨_, h0⟩, P₁.inter_spec ⟨_, h1⟩]
  masterIdx := Nat.pair P₀.masterIdx P₁.masterIdx
  masterIdx_spec := by
    simp only [prodEnum_apply, unpair_pair_fst, unpair_pair_snd, P₀.masterIdx_spec,
      P₁.masterIdx_spec, prod_master]

end DomainTheory.NeighbourhoodSystems
