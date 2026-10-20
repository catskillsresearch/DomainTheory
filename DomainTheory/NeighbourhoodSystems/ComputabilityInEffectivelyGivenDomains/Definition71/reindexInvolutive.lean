module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}

namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- **Reindexing a computable presentation along a primitive-recursive involution.** Given
`φ : ℕ → ℕ` with `φ ∘ φ = id` (so `φ` is automatically a bijection, with itself as inverse) and
`Nat.Primrec φ`, transport `P`'s enumeration and both deciders along `φ`: `X' n := P.X (φ n)`.
Every one of Scott's structural fields transfers by straightforward reindexing (`RecDecidable.comp`
against the pairwise-`φ`-reindexing code), so this is a genuinely choice-free construction — used
to re-point a presentation's `0`-th index at an arbitrary target (Theorem 8.8(b)'s `D₀ ≅ D` shift,
via `eIdx`). -/
def reindexInvolutive (P : ComputablePresentation V) (φ : ℕ → ℕ)
    (hφinv : Function.Involutive φ) (hφp : Nat.Primrec φ) : ComputablePresentation V where
  X n := P.X (φ n)
  mem_X n := P.mem_X (φ n)
  surj := fun {Y} hY => by
    obtain ⟨k, hk⟩ := P.surj hY
    exact ⟨φ k, by rw [hφinv k]; exact hk⟩
  interEq_computable := by
    have hreindex : Nat.Primrec (fun t : ℕ =>
        Nat.pair (φ t.unpair.1) (Nat.pair (φ t.unpair.2.unpair.1) (φ t.unpair.2.unpair.2))) :=
      (hφp.comp Nat.Primrec.left).pair
        ((hφp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (hφp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp hreindex)
    simp only [unpair_pair_fst, unpair_pair_snd]
  cons_computable := by
    have hreindex : Nat.Primrec (fun t : ℕ =>
        Nat.pair (φ t.unpair.1) (φ t.unpair.2)) :=
      (hφp.comp Nat.Primrec.left).pair (hφp.comp Nat.Primrec.right)
    refine RecDecidable.of_iff (fun t => ?_) (P.cons_computable.comp hreindex)
    simp only [unpair_pair_fst, unpair_pair_snd]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨φ k, hk⟩
    · rintro ⟨k, hk⟩; exact ⟨φ k, by rwa [hφinv]⟩
  inter n m := φ (P.inter (φ n) (φ m))
  inter_primrec := by
    have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (φ t.unpair.1) (φ t.unpair.2)) :=
      (hφp.comp Nat.Primrec.left).pair (hφp.comp Nat.Primrec.right)
    exact (hφp.comp ((P.inter_primrec.comp hreindex))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  inter_spec {n m} h := by
    show P.X (φ (φ (P.inter (φ n) (φ m)))) = P.X (φ n) ∩ P.X (φ m)
    rw [hφinv]
    obtain ⟨k, hk⟩ := h
    exact P.inter_spec ⟨φ k, hk⟩
  masterIdx := φ P.masterIdx
  masterIdx_spec := by show P.X (φ (φ P.masterIdx)) = V.master; rw [hφinv]; exact P.masterIdx_spec

end ComputablePresentation

end DomainTheory.NeighbourhoodSystems
